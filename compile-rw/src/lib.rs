lalrpop_mod!(grammar);

use core::fmt::{Display, Formatter, Result};

use hashbrown::{HashMap, HashSet};
use lalrpop_util::lalrpop_mod;
use prettyplease::unparse;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{ToTokens, TokenStreamExt, format_ident, quote};
use symbol_table::GlobalSymbol as Symbol;
use syn::parse2;

use grammar::RewritesParser;

type Constant = i32;

#[derive(Debug, Clone)]
struct Rewrite {
    lhs: Pattern,
    rhs: Pattern,
}

#[derive(Debug, Clone)]
enum Pattern {
    Variable(Symbol),
    Constant(Constant),
    Wildcard,
    Unary(Symbol, Box<Pattern>),
    Binary(Symbol, Box<Pattern>, Box<Pattern>),
}

// The LHS patterns of rewrites are converted into relational queries.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Query {
    // The variable for the root ID of the pattern. Needed so we know what to union with.
    root: Symbol,
    atoms: Vec<Atom>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Atom {
    relation: Symbol,
    terms: Vec<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Term {
    Variable(Symbol),
    Constant(Constant),
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct NeededTrie {
    relation: Symbol,
    is_delta: bool,
    constants: Vec<(usize, Constant)>,
    // For each step in the order, store a set of columns that must hold the same value.
    column_order: Vec<Vec<usize>>,
}

impl Atom {
    fn constants(&self) -> Vec<(usize, Constant)> {
        let mut constants = vec![];
        for (term_idx, term) in self.terms.iter().enumerate() {
            if let Term::Constant(cons) = term {
                constants.push((term_idx, *cons));
            }
        }
        constants
    }
}

impl Display for NeededTrie {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{}_c",
            if self.is_delta { "delta_" } else { "" },
            self.relation
        )?;
        for (column, cons) in &self.constants {
            write!(f, "_{}_{}", column, cons)?;
        }
        write!(f, "_v")?;
        for columns in &self.column_order {
            write!(f, "_")?;
            for column in columns {
                write!(f, "_{}", column)?;
            }
        }
        Ok(())
    }
}

impl ToTokens for NeededTrie {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(Ident::new(&format!("{}", self), Span::call_site()))
    }
}

// Flatten a nested pattern into a relational qeury - see "Relational E-matching" by Zhang et al.
fn pattern_to_query(pattern: &Pattern) -> Query {
    fn pattern_to_query_helper(pattern: &Pattern, atoms: &mut Vec<Atom>) -> Term {
        match pattern {
            Pattern::Variable(var) => Term::Variable(*var),
            Pattern::Constant(cons) => {
                let var = format!("_cons_{cons}").into();
                let atom = Atom {
                    relation: "Constant".into(),
                    terms: vec![Term::Variable(var), Term::Constant(*cons)],
                };
                atoms.push(atom);
                Term::Variable(var)
            }
            Pattern::Wildcard => Term::Wildcard,
            Pattern::Unary(op, input) => {
                let input = pattern_to_query_helper(input, atoms);
                let var = format!("_root_{}", atoms.len()).into();
                let atom = Atom {
                    relation: *op,
                    terms: vec![Term::Variable(var), input],
                };
                atoms.push(atom);
                Term::Variable(var)
            }
            Pattern::Binary(op, lhs, rhs) => {
                let lhs = pattern_to_query_helper(lhs, atoms);
                let rhs = pattern_to_query_helper(rhs, atoms);
                let var = format!("_root_{}", atoms.len()).into();
                let atom = Atom {
                    relation: *op,
                    terms: vec![Term::Variable(var), lhs, rhs],
                };
                atoms.push(atom);
                Term::Variable(var)
            }
        }
    }

    let mut atoms = vec![];
    let root = pattern_to_query_helper(pattern, &mut atoms);
    let Term::Variable(root) = root else { panic!() };
    Query { root, atoms }
}

// Determine the variable order for the WCOJ over a query.
fn variable_order(query: &Query, delta_idx: usize) -> Vec<Symbol> {
    // For now, we just order variables by # of occurrences in the query. Occurrences inside delta
    // atoms are more heavily weighed, since delta relations will be smaller than normal relations.
    const DELTA_WEIGHT: isize = 10;
    let mut num_occurs: HashMap<Symbol, isize> = HashMap::new();
    for (atom_idx, atom) in query.atoms.iter().enumerate() {
        for term in &atom.terms {
            if let Term::Variable(var) = term {
                *num_occurs.entry(*var).or_default() += if atom_idx == delta_idx {
                    DELTA_WEIGHT
                } else {
                    1
                };
            }
        }
    }

    let mut order: Vec<_> = num_occurs.keys().cloned().collect();
    order.sort_by_key(|var| -num_occurs[var]);
    order
}

// For each variable in a query, determine the set of atoms (indices) that contain that variable, and
// for each atom at what column indices that variable appears.
type AtomsContaining = HashMap<Symbol, HashMap<usize, Vec<usize>>>;
fn atoms_containing(query: &Query) -> AtomsContaining {
    let mut atoms_containing = AtomsContaining::new();
    for (atom_idx, atom) in query.atoms.iter().enumerate() {
        for (column_idx, term) in atom.terms.iter().enumerate() {
            if let Term::Variable(var) = term {
                // The Vec acts as a set since per atom, column indices are visited once, in order.
                atoms_containing
                    .entry(*var)
                    .or_default()
                    .entry(atom_idx)
                    .or_default()
                    .push(column_idx);
            }
        }
    }
    atoms_containing
}

fn emit_wcoj(
    query: &Query,
    delta_idx: usize,
    atoms_containing: &AtomsContaining,
    var_order: &Vec<Symbol>,
    rule_tries: &Vec<NeededTrie>,
) -> TokenStream {
    // Emits one nested loop of the WCOJ.
    fn emit_wcoj_helper(
        query: &Query,
        delta_idx: usize,
        atoms_containing: &AtomsContaining,
        var_order: &[Symbol],
    ) -> TokenStream {
        if let Some((var, rest)) = var_order.split_first() {
            let var_iden = format_ident!("{}", var.as_str());
            
            // Figure out which involved trie is smallest.
            let mut smallest = quote! {};
            let mut first = true;
            for (atom_idx, _) in &atoms_containing[var] {
                let trievar = format_ident!("trie_{}", atom_idx);
                if first {
                    first = false;
                    smallest = quote! {
                        #smallest
                        let mut smallest_idx = #atom_idx;
                        let mut smallest_trie = #trievar;
                    };
                } else {
                    smallest = quote! {
                        #smallest
                        if #trievar.try_internal().unwrap().len() < smallest_trie.try_internal().unwrap().len() {
                            smallest_idx = #atom_idx;
                            smallest_trie = #trievar;
                        }
                    };
                }
            }

            // Check that the scanned value is in the other tries. At the same time, redefine
            // `trie_N` for the next level of the WCOJ.
            let probe: TokenStream = atoms_containing[var]
                .iter()
                .map(|(atom_idx, _)| {
                    let trievar = format_ident!("trie_{}", atom_idx);
                    quote! {
                        let #trievar =
                            if #atom_idx == smallest_idx {
                                child_of_smallest
                            } else {
                                let Some(child) = #trievar.try_internal().unwrap().get(#var_iden) else { continue; };
                                child
                            };
                    }
                })
                .collect();

            // Emit the rest of the WCOJ.
            let nested = emit_wcoj_helper(query, delta_idx, atoms_containing, rest);

            quote! {
                #smallest
                for (#var_iden, child_of_smallest) in smallest_trie.try_internal().unwrap() {
                    #probe
                    #nested
                } }
        } else {
            // Construct the nodes in the e-graph for the RHS.
            quote! { todo!() }
        }
    }

    let init: TokenStream = rule_tries
        .iter()
        .enumerate()
        .map(|(idx, needed_trie)| {
            let trievar = format_ident!("trie_{}", idx);
            quote! { let #trievar = &tries.#needed_trie; }
        })
        .collect();
    let block = emit_wcoj_helper(query, delta_idx, atoms_containing, var_order);
    quote! {
        {
            #init
            #block
        }
    }
}

pub fn compile_rw(contents: &str) -> String {
    let rws = RewritesParser::new().parse(contents).unwrap();

    // Implementing the LHS matching of each rule is the "hard" part.
    let queries: Vec<_> = rws.iter().map(|rw| pattern_to_query(&rw.lhs)).collect();

    // First, we need to determine the order that variables are matched in each query. We determine
    // this order differently for every delta query of each original query. Each delta query's order
    // is identified by the index of the delta atom in the original query (hence the nested Vecs).
    let var_orders: Vec<Vec<_>> = queries
        .iter()
        .map(|query| {
            (0..query.atoms.len())
                .map(|delta_idx| variable_order(query, delta_idx))
                .collect()
        })
        .collect();
    let atoms_containings: Vec<_> = queries
        .iter()
        .map(|query| atoms_containing(query))
        .collect();

    // Second, we need to determine the set of tries that are needed. Each trie is identified by:
    // 1. A relation the trie is indexing (an identifier + is delta or not).
    // 2. An order to index the columns of the relation in - each step of the order is a set of
    //    column indices, not just a single column index, because a query may want to index multiple
    //    columns simultaneously, enforcing the constraint that their values are equal.
    // The set of needed tries is shared across all rewrites.
    let mut needed_tries = HashSet::new();
    let mut query_tries = vec![];
    for query_idx in 0..queries.len() {
        let query = &queries[query_idx];
        let atoms_containing = &atoms_containings[query_idx];
        let mut tries_for_query = vec![];
        for delta_idx in 0..query.atoms.len() {
            let mut rule_tries: Vec<_> = (0..query.atoms.len())
                .map(|atom_idx| NeededTrie {
                    relation: query.atoms[atom_idx].relation,
                    is_delta: atom_idx == delta_idx,
                    constants: query.atoms[atom_idx].constants(),
                    column_order: vec![],
                })
                .collect();
            let var_order = &var_orders[query_idx][delta_idx];
            for var in var_order {
                let atoms = &atoms_containing[var];
                for (atom_idx, columns) in atoms {
                    rule_tries[*atom_idx].column_order.push(columns.clone());
                }
            }
            tries_for_query.push(rule_tries.clone());
            needed_tries.extend(rule_tries);
        }
        query_tries.push(tries_for_query);
    }

    // Third, emit the code that constructs the tries.
    let mut trie_struct = quote! {};
    trie_struct.extend(needed_tries.iter().map(|trie| {
        quote! {
            #trie: Trie,
        }
    }));
    trie_struct = quote! {
        #[derive(Default)]
        struct Tries {
            #trie_struct
        }
    };

    // Fourth, emit the code that implements WCOJ.
    let mut wcojs = quote! {};
    for query_idx in 0..queries.len() {
        let query = &queries[query_idx];
        let atoms_containing = &atoms_containings[query_idx];
        for delta_idx in 0..query.atoms.len() {
            let var_order = &var_orders[query_idx][delta_idx];
            let rule_tries = &query_tries[query_idx][delta_idx];
            wcojs.extend(emit_wcoj(
                query,
                delta_idx,
                atoms_containing,
                var_order,
                rule_tries,
            ));
        }
    }

    // Finally, emit the top level rewriting function.
    let rw_fn = quote! {
        use crate::saturator::Saturator;
        use crate::trie::Trie;

        #trie_struct

        fn apply_rws(saturator: &mut Saturator) {
            let tries: Tries = todo!();

            #wcojs
        }
    };
    // Format the Rust code so it's (more) pretty to look at.
    unparse(&parse2(rw_fn).unwrap())
}

#[cfg(test)]
mod tests {
    use symbol_table::GlobalSymbol as Symbol;

    use crate::*;

    #[test]
    fn pattern_to_query1() {
        let rw = "(rw (Add a 0) a)";
        let rw = RewritesParser::new().parse(rw).unwrap();
        let query = pattern_to_query(&rw[0].lhs);
        assert_eq!(
            query,
            Query {
                root: "_root_1".into(),
                atoms: vec![
                    Atom {
                        relation: "Constant".into(),
                        terms: vec![Term::Variable("_cons_0".into()), Term::Constant(0)]
                    },
                    Atom {
                        relation: "Add".into(),
                        terms: vec![
                            Term::Variable("_root_1".into()),
                            Term::Variable("a".into()),
                            Term::Variable("_cons_0".into())
                        ]
                    }
                ]
            }
        );
    }

    #[test]
    fn var_order1() {
        let rw = "(rw (Add a (Sub b a)) b)";
        let rw = RewritesParser::new().parse(rw).unwrap();
        let query = pattern_to_query(&rw[0].lhs);
        let var_order = variable_order(&query, 0);
        assert!(
            var_order == vec!["a".into(), "_root_0".into(), "b".into(), "_root_1".into()]
                || var_order == vec!["_root_0".into(), "a".into(), "b".into(), "_root_1".into()]
        );
        let atoms_containing = atoms_containing(&query);
        assert_eq!(
            atoms_containing[&Symbol::from("a")][&0],
            [2].into_iter().collect::<Vec<_>>()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("a")][&1],
            [1].into_iter().collect::<Vec<_>>()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("b")][&0],
            [1].into_iter().collect::<Vec<_>>()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("_root_0")][&0],
            [0].into_iter().collect::<Vec<_>>()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("_root_0")][&1],
            [2].into_iter().collect::<Vec<_>>()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("_root_1")][&1],
            [0].into_iter().collect::<Vec<_>>()
        );
    }
}
