use hashbrown::{HashMap, HashSet};
use lalrpop_util::lalrpop_mod;
use symbol_table::GlobalSymbol as Symbol;

use grammar::RewritesParser;

#[derive(Debug, Clone)]
struct Rewrite {
    lhs: Pattern,
    rhs: Pattern,
}

#[derive(Debug, Clone)]
enum Pattern {
    Variable(Symbol),
    Constant(i64),
    Wildcard,
    Unary(Symbol, Box<Pattern>),
    Binary(Symbol, Box<Pattern>, Box<Pattern>),
}

lalrpop_mod!(grammar);

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
    Constant(i64),
    Wildcard,
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

fn atoms_containing(query: &Query) -> HashMap<Symbol, HashSet<usize>> {
    let mut atoms_containing: HashMap<Symbol, HashSet<usize>> = HashMap::new();
    for (atom_idx, atom) in query.atoms.iter().enumerate() {
        for term in &atom.terms {
            if let Term::Variable(var) = term {
                atoms_containing.entry(*var).or_default().insert(atom_idx);
            }
        }
    }
    atoms_containing
}

pub fn compile_rw(contents: &str) {
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
            atoms_containing[&Symbol::from("a")],
            [0, 1].into_iter().collect()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("b")],
            [0].into_iter().collect()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("_root_0")],
            [0, 1].into_iter().collect()
        );
        assert_eq!(
            atoms_containing[&Symbol::from("_root_1")],
            [1].into_iter().collect()
        );
    }
}
