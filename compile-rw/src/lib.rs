use grammar::RewritesParser;
use lalrpop_util::lalrpop_mod;
use symbol_table::GlobalSymbol as Symbol;

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
                let var = format!("_root_{}", atoms.len()).into();
                let input = pattern_to_query_helper(input, atoms);
                let atom = Atom {
                    relation: *op,
                    terms: vec![Term::Variable(var), input],
                };
                atoms.push(atom);
                Term::Variable(var)
            }
            Pattern::Binary(op, lhs, rhs) => {
                let var = format!("_root_{}", atoms.len()).into();
                let lhs = pattern_to_query_helper(lhs, atoms);
                let rhs = pattern_to_query_helper(rhs, atoms);
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

pub fn compile_rw(contents: &str) {
    let rws = RewritesParser::new().parse(contents).unwrap();
    let queries: Vec<_> = rws.iter().map(|rw| pattern_to_query(&rw.lhs)).collect();
}

#[cfg(test)]
mod tests {
    use crate::grammar::RewritesParser;
    use crate::{Atom, Query, Term, pattern_to_query};

    #[test]
    fn pattern_to_query1() {
        let rw = "(rw (Add a 0) a)";
        let rw = RewritesParser::new().parse(rw).unwrap();
        let query = pattern_to_query(&rw[0].lhs);
        assert_eq!(
            query,
            Query {
                root: "_root_0".into(),
                atoms: vec![
                    Atom {
                        relation: "Constant".into(),
                        terms: vec![Term::Variable("_cons_0".into()), Term::Constant(0)]
                    },
                    Atom {
                        relation: "Add".into(),
                        terms: vec![
                            Term::Variable("_root_0".into()),
                            Term::Variable("a".into()),
                            Term::Variable("_cons_0".into())
                        ]
                    }
                ]
            }
        );
    }
}
