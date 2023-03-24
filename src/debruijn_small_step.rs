use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;
use std::fmt::Display;
use std::str::FromStr;
use crate::benchmarks;
use crate::destructive_rewrite::{MatchOverLanguage, DestructiveRewrite};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct DeBruijnIndex(u32);

impl DeBruijnIndex {
    fn increment(&self) -> Self {
        DeBruijnIndex(self.0 + 1)
    }

    fn decrement(&self) -> Self {
        if self.0 > 0 {
            DeBruijnIndex(self.0 - 1)
        } else {
            panic!("Cannot decrement DeBruijnIndex 0")
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct InvalidIndexError;

impl FromStr for DeBruijnIndex {
    type Err = InvalidIndexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with('@') {
            s[1..]
                .parse()
                .map(DeBruijnIndex)
                .map_err(|_| InvalidIndexError)
        } else {
            Err(InvalidIndexError)
        }
    }
}

impl Display for DeBruijnIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

define_language! {
    enum DeBruijn{
        Bool(bool),
        Num(i32),

        "+" = Add([Id; 2]),
        "=" = Eq([Id; 2]),

        "fix" = Fix([Id; 1]),
        "app" = App([Id; 2]),
        "lam" = Lam([Id; 1]),
        "let" = Let([Id; 2]),
        "sub" = Sub([Id; 3]),
        "if" = If([Id; 3]),

        "shift" = Shift([Id; 2]),

        Index(DeBruijnIndex),
    }
}

fn increment_id(id: Id, increment: usize) -> Id {
    let id_as_usize: usize = id.into();
    (id_as_usize + increment).into()
}

impl DeBruijn {
    fn num(&self) -> Option<i32> {
        match self {
            DeBruijn::Num(n) => Some(*n),
            _ => None,
        }
    }

    fn index(&self) -> Option<DeBruijnIndex> {
        match self {
            DeBruijn::Index(dbi) => Some(*dbi),
            _ => None
        }
    }

    fn increment_id(&self, increment: usize) -> Self {
        match self {
            DeBruijn::Add([id1, id2]) => {
                DeBruijn::Add([increment_id(*id1, increment), increment_id(*id2, increment)])
            }
            DeBruijn::Eq([id1, id2]) => {
                DeBruijn::Eq([increment_id(*id1, increment), increment_id(*id2, increment)])
            }
            DeBruijn::App([id1, id2]) => {
                DeBruijn::App([increment_id(*id1, increment), increment_id(*id2, increment)])
            }
            DeBruijn::Lam([id]) => DeBruijn::Lam([increment_id(*id, increment)]),
            DeBruijn::Let([id2, id3]) => {
                DeBruijn::Let([increment_id(*id2, increment), increment_id(*id3, increment)])
            }
            DeBruijn::Fix([id1]) => {
                DeBruijn::Fix([increment_id(*id1, increment)])
            }
            DeBruijn::If([id1, id2, id3]) => DeBruijn::If([
                increment_id(*id1, increment),
                increment_id(*id2, increment),
                increment_id(*id3, increment),
            ]),
            DeBruijn::Sub([id1, id2, id3]) => DeBruijn::Sub([
                increment_id(*id1, increment),
                increment_id(*id2, increment),
                increment_id(*id3, increment),
            ]),
            DeBruijn::Shift([id1, id2]) => DeBruijn::Shift([
                increment_id(*id1, increment),
                increment_id(*id2, increment),
            ]),
            DeBruijn::Bool(_) | DeBruijn::Num(_) | DeBruijn::Index(_) => self.to_owned(),
        }
    }
}

type EGraph = egg::EGraph<DeBruijn, DeBruijnAnalysis>;

#[derive(Default)]
struct DeBruijnAnalysis;

#[derive(Debug)]
struct Data {
    constant: Option<(DeBruijn, PatternAst<DeBruijn>)>,
    index: Option<DeBruijnIndex>,
}

fn eval_constant(egraph: &EGraph, enode: &DeBruijn) -> Option<(DeBruijn, PatternAst<DeBruijn>)> {
    let x = |i: &Id| egraph[*i].data.constant.as_ref().map(|c| &c.0);
    match enode {
        DeBruijn::Num(n) => Some((enode.clone(), format!("{}", n).parse().unwrap())),
        DeBruijn::Bool(b) => Some((enode.clone(), format!("{}", b).parse().unwrap())),
        DeBruijn::Add([a, b]) => Some((
            DeBruijn::Num(x(a)?.num()? + x(b)?.num()?),
            format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        DeBruijn::Eq([a, b]) => Some((
            DeBruijn::Bool(x(a)? == x(b)?),
            format!("(= {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        _ => None,
    }
}

fn eval_index(enode: &DeBruijn) -> Option<DeBruijnIndex> {
    match enode {
        DeBruijn::Index(i) => Some(*i),
        _ => None,
    }
}

impl Analysis<DeBruijn> for DeBruijnAnalysis {
    type Data = Data;
    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        let res1 = merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        });
        let res2 = merge_option(&mut to.index, from.index, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal indices");
            DidMerge(false, false)
        });
        res1 | res2
    }

    fn make(egraph: &EGraph, enode: &DeBruijn) -> Data {
        let constant = eval_constant(egraph, enode);
        let index = eval_index(enode);
        Data { constant, index }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant.clone() {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &c.0.to_string().parse().unwrap(),
                    &c.1,
                    &Default::default(),
                    "analysis".to_string(),
                );
            } else {
                let const_id = egraph.add(c.0);
                egraph.union(id, const_id);
            }
        }
        if let Some(i) = &egraph[id].data.index {
            // TODO: explanation
            let index_id = egraph.add(DeBruijn::Index(*i));
            egraph.union(id, index_id);
        }
    }
}

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn is_const(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v]].data.constant.is_some()
}

// Indices should live in a singleton e-class
fn is_both_index(i1: Var, i2: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        egraph[subst[i1]].data.index.is_some()
        && egraph[subst[i2]].data.index.is_some()
    }
}


fn rules() -> Vec<Rewrite<DeBruijn, DeBruijnAnalysis>> {
    vec![
        // open term rules
        rw!("if-true";  "(if true ?then ?else)" => {
            DestructiveRewrite {
                original_pattern: "(if true ?then ?else)".parse().unwrap(),
                add_pattern: "?then".parse().unwrap()
            }
        }),
        rw!("if-false"; "(if false ?then ?else)" => {
            DestructiveRewrite {
                original_pattern: "(if false ?then ?else)".parse().unwrap(),
                add_pattern: "?else".parse().unwrap()
            }
        }),
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
        rw!("fix";      "(fix ?e)"          => "(let (fix ?e) ?e)"),
        // sub generators
        rw!("beta";     "(app (lam ?body) ?e)" => "(sub @0 ?e ?body)"),
        rw!("let";     "(let ?v ?e)" => "(sub @0 ?v ?e)"),
        // sub rules
        rw!("sub-index"; "(sub ?i1 ?e ?i2)" => {
            SubIndex {
                sub_index: var("?i1"),
                sub_e: var("?e"),
                matched_index: var("?i2"),
            }
        } if is_both_index(var("?i1"), var("?i2"))),
        rw!("sub-const"; "(sub ?i ?e ?c)" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e ?c)".parse().unwrap(),
                add_pattern: "?c".parse().unwrap(),
            }
        } if is_const(var("?c"))),
        rw!("sub-apply"; "(sub ?i ?e (app ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e (app ?a ?b))".parse().unwrap(),
                add_pattern: "(app (sub ?i ?e ?a) (sub ?i ?e ?b))".parse().unwrap(),
            }
        }),
        rw!("sub-add"; "(sub ?i ?e (+ ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e (+ ?a ?b))".parse().unwrap(),
                add_pattern: "(+ (sub ?i ?e ?a) (sub ?i ?e ?b))".parse().unwrap(),
            }
        }),
        rw!("sub-eq"; "(sub ?i ?e (= ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e (= ?a ?b))".parse().unwrap(),
                add_pattern: "(= (sub ?i ?e ?a) (sub ?i ?e ?b))".parse().unwrap(),
            }
        }),
        rw!("sub-if"; "(sub ?i ?e (if ?cond ?then ?else))" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e (if ?cond ?then ?else))".parse().unwrap(),
                add_pattern: "(if (sub ?i ?e ?cond) (sub ?i ?e ?then) (sub ?i ?e ?else))".parse().unwrap(),
            }
        }),
        rw!("sub-let"; "(sub ?i ?e1 (let ?v ?e2))" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e1 (let ?v ?e2))".parse().unwrap(),
                add_pattern: "(let ?v (sub (shift @0 ?i) (shift @0 ?e1) ?e2))".parse().unwrap(),
            }
        }),
        rw!("sub-lam"; "(sub ?i ?e1 (lam ?body))" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e1 (lam ?body))".parse().unwrap(),
                add_pattern: "(lam (sub (shift @0 ?i) (shift @0 ?e1) ?body))".parse().unwrap(),
            }
        }),
        // shifting - this is to shift free variables when we substitute over a lambda/let/fix.
        rw!("shift";    "(shift ?i1 ?i2)"  => { ShiftIndex { min_index: var("?i1"), index: var("?i2") }} if is_both_index(var("?i1"), var("?i2"))),
        rw!("shift-const"; "(shift ?i ?c)" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i ?c)".parse().unwrap(),
                add_pattern: "?c".parse().unwrap(),
            }
        } if is_const(var("?c"))),
        rw!("shift-apply"; "(shift ?i (app ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i (app ?a ?b))".parse().unwrap(),
                add_pattern: "(app (shift ?i ?a) (shift ?i ?b))".parse().unwrap(),
            }
        }),
        rw!("shift-add"; "(shift ?i (+ ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i (+ ?a ?b))".parse().unwrap(),
                add_pattern: "(+ (shift ?i ?a) (shift ?i ?b))".parse().unwrap(),
            }
        }),
        rw!("shift-eq"; "(shift ?i (= ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i (= ?a ?b))".parse().unwrap(),
                add_pattern: "(= (shift ?i ?a) (shift ?i ?b))".parse().unwrap(),
            }
        }),
        rw!("shift-if"; "(shift ?i (if ?cond ?then ?else))" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i (if ?cond ?then ?else))".parse().unwrap(),
                add_pattern: "(if (shift ?i ?cond) (shift ?i ?then) (shift ?i ?else))".parse().unwrap(),
            }
        }),
        // shift doesn't work on bound indices
        rw!("shift-let"; "(shift ?i (let ?v ?e))" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i (let ?v ?e))".parse().unwrap(),
                add_pattern: "(let (shift ?i ?v) (shift (shift @0 ?i) ?e))".parse().unwrap(),
            }
        }),
        rw!("shift-lam"; "(shift ?i (lam ?e))" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i (lam ?e))".parse().unwrap(),
                add_pattern: "(lam (shift (shift @0 ?i) ?e))".parse().unwrap(),
            }
        }),
        // rw!("shift-fix"; "(shift ?i (fix ?e))" => "(fix (shift (shift @0 ?i) ?e))"),
    ]
}

impl MatchOverLanguage for DeBruijn {
    fn match_over<P>(&self, candidate: &Self, mut match_child: P) -> bool
    where Self: Sized,
          P: FnMut(&Id, &Id) -> bool,
    {
        return false;
        use DeBruijn::*;
        match (self, candidate) {
            (Bool(b_self), Bool(b_cand)) => b_self == b_cand,
            (Num(n_self), Num(n_cand)) => n_self == n_cand,
            (Index(i_self), Index(i_cand)) => i_self == i_cand,
            (Add([e1_self, e2_self]), Add([e1_cand, e2_cand])) => {
                match_child(e1_self, e1_cand)
                && match_child(e2_self, e2_cand)
            }
            (Eq([e1_self, e2_self]), Eq([e1_cand, e2_cand])) => {
                match_child(e1_self, e1_cand)
                && match_child(e2_self, e2_cand)
            }
            (App([e1_self, e2_self]), App([e1_cand, e2_cand])) => {
                match_child(e1_self, e1_cand)
                && match_child(e2_self, e2_cand)
            }
            (Let([e1_self, e2_self]), Let([e1_cand, e2_cand])) => {
                match_child(e1_self, e1_cand)
                && match_child(e2_self, e2_cand)
            }
            (Shift([e1_self, e2_self]), Shift([e1_cand, e2_cand])) => {
                match_child(e1_self, e1_cand)
                && match_child(e2_self, e2_cand)
            }
            (Lam([e_self]), Lam([e_cand])) => {
                match_child(e_self, e_cand)
            }
            (Fix([e_self]), Fix([e_cand])) => {
                match_child(e_self, e_cand)
            }
            (Sub([e1_self, e2_self, e3_self]), Sub([e1_cand, e2_cand, e3_cand])) => {
                match_child(e1_self, e1_cand)
                && match_child(e2_self, e2_cand)
                && match_child(e3_self, e3_cand)
            }
            (If([e1_self, e2_self, e3_self]), If([e1_cand, e2_cand, e3_cand])) => {
                match_child(e1_self, e1_cand)
                && match_child(e2_self, e2_cand)
                && match_child(e3_self, e3_cand)
            }
            _ => false,
        }
    }
}

struct ShiftIndex {
    min_index: Var,
    index: Var,
}

/// Shifts a DeBruijn Index if it's greater than min_index.
///
/// The idea is to only shift free vars.
impl Applier<DeBruijn, DeBruijnAnalysis> for ShiftIndex {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<DeBruijn>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let index_id = subst[self.index];
        let min_dbi_id = subst[self.min_index];
        // If we reach this rule, it is assumed that these eclasses are both a
        // singleton eclass containing only an index.
        let index_dbi = egraph[index_id].data.index.unwrap();
        let min_dbi = egraph[min_dbi_id].data.index.unwrap();
        // Remove the shift we matched.
        egraph[eclass].nodes = egraph[eclass].nodes
            .to_owned()
            .into_iter()
            .filter(|node| match node {
                DeBruijn::Shift([id1, id2]) if *id1 == min_dbi_id && *id2 == index_id => false,
                _ => true,
            })
            .collect();
        // TODO: can we just add this directly to egraph[eclass].nodes?
        let shifted_index_id = if index_dbi.0 >= min_dbi.0 {
            egraph.add(DeBruijn::Index(index_dbi.increment()))
        } else {
            egraph.add(DeBruijn::Index(index_dbi))
        };
        egraph.union(shifted_index_id, eclass);
        vec!(shifted_index_id, eclass)
    }
}

struct SubIndex {
    sub_index: Var,
    sub_e: Var,
    matched_index: Var,
}

impl Applier<DeBruijn, DeBruijnAnalysis> for SubIndex {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        // Don't confuse this with sub - these are two different things.
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<DeBruijn>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let sub_index_id = subst[self.sub_index];
        let sub_e_id = subst[self.sub_e];
        let matched_index_id = subst[self.matched_index];
        let sub_index = egraph[sub_index_id].data.index.unwrap();
        let matched_index = egraph[matched_index_id].data.index.unwrap();
        // Remove the sub we matched.
        egraph[eclass].nodes = egraph[eclass].nodes
            .to_owned()
            .into_iter()
            .filter(|node| match node {
                DeBruijn::Sub([id1, id2, id3])
                    if *id1 == sub_index_id
                    && *id2 == sub_e_id
                    && *id3 == matched_index_id => false,
                _ => true,
            })
            .collect();
        // If they're equal, substitute
        let new_expr_id = if matched_index.0 == sub_index.0 {
            sub_e_id
        // If the matched index is greater, then it must be free. We need to
        // decrement it.
        } else if matched_index.0 > sub_index.0 {
            egraph.add(DeBruijn::Index(matched_index.decrement()))
        // Otherwise, it's bound and we can't touch it.
        } else {
            egraph.add(DeBruijn::Index(matched_index))
        };
        egraph.union(new_expr_id, eclass);
        vec!(new_expr_id, eclass)
    }
}

egg::test_fn! {
    dbsmallstep_simple_let, rules(),
    "(let 4 (+ 1 @0))"
    =>
    "5",
}

egg::test_fn! {
    dbsmallstep_simple_let2, rules(),
    "(let 4 (lam @1))"
    =>
    "(lam 4)",
}

egg::test_fn! {
    dbsmallstep_simple_let3, rules(),
    "(let 4 (lam @0))"
    =>
    "(lam @0)",
}

egg::test_fn! {
    dbsmallstep_single_lam, rules(),
    "(app (lam (+ 1 @0)) 2)" => "3",
}

egg::test_fn! {
    dbsmallstep_double_app, rules(),
    "(app (app (lam (lam @1)) 1) 2)" => "1",
}

egg::test_fn! {
    dbsmallstep_four_let, rules(),
    "(let (lam (+ 1 @0))
     (let (lam (+ 2 @0))
     (let (lam (+ 3 @0))
     (let (lam (+ 4 @0))
      (app @3 (app @2 (app @1 (app @0 0))))))))
    "
    =>
    "10"
}

egg::test_fn! {
    dbsmallstep_recursive_let, rules(),
    "(let (lam (+ 1 @0))
     (let (lam (app @1 (app @1 @0)))
     (let (lam (app @2 (app @1 @0)))
      (app @2 (app @1 (app @0 0))))))
    "
    =>
    "6"
}

egg::test_fn! {
    dbsmallstep_compose, rules(),
    "(let
        (lam (lam (lam (app @2 (app @1 @0)))))
        (let 
            (lam (+ @0 1))
            (app (app @1 @0) @0)
        )
    )"
    =>
    "(lam (+ @0 2))"
}

egg::test_fn! {
    dbsmallstep_compose_2, rules(),
    "(let
        (lam (lam (lam (app @2 (app @1 @0)))))
        (let
            (lam (+ @0 1))
            (app (app @1 (app (app @1 @0) @0)) @0)
        )
    )"
    =>
    "(lam (+ @0 3))"
}

egg::test_fn! {
    dbsmallstep_double_let_lambdas, rules(),
    "(let
        (lam (+ @0 1))
        (let 
            (lam (+ @0 2))
            (lam (app @2 (app @1 @0)))
        )
    )"
    =>
    "(lam (+ @0 3))",
}

egg::test_fn! {
    dbsmallstep_compose_many_many_1, rules(),
    "(let (lam (lam (lam (app @2 (app @1 @0)))))
     (let (lam (+ @0 1))
     (let (lam (app (app @2 @0) @0))
     (app @0
     (app @0
     (app @0
       @1))))))"
    =>
    "(lam (+ @0 8))"
}

egg::test_fn! {
    dbsmallstep_compose_many_many_1_small, rules(),
    "(let (lam (lam (lam (app @2 (app @1 @0)))))
     (let (lam (app (app @1 @0) @0))
     (let (lam (+ @0 1))
     (app @1
       @0))))"
    =>
    "(lam (+ @0 2))"
}

egg::test_fn! {
    dbsmallstep_fib, rules(),
    "(let (fix (lam
        (if (= @0 0)
            0
        (if (= @0 1)
            1
        (+ (app @1
                (+ @0 -1))
            (app @1
                (+ @0 -2)))))))
        (app @0 5))"
    =>
    "5"
}

// #[test]
// fn lambda_dbsmallstep_fib_range() {
//     let range = 0..30;
//     for n in range {
//         let (start, goal) = benchmarks::fib_sexprs_db(n);
//         let start = start.parse().unwrap();
//         let goal = goal.parse().unwrap();
//         let runner_name = std::format!("lambda_db_fib_{n}");
//         eprintln!("####### {}", runner_name);
//
//         benchmarks::test_runner(&runner_name, None, &rules(), start, &[goal], None, true);
//         eprintln!("\n\n\n")
//     }
// }
