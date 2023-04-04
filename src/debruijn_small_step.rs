use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;
use fxhash::FxHashMap as HashMap;
use std::fmt::Display;
use std::str::FromStr;
use crate::benchmarks;

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
    previous_rewrites: HashSet<(Symbol, Subst, PatternAst<DeBruijn>)>,
    constant: Option<(DeBruijn, PatternAst<DeBruijn>)>,
}

fn eval(egraph: &EGraph, enode: &DeBruijn) -> Option<(DeBruijn, PatternAst<DeBruijn>)> {
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

impl Analysis<DeBruijn> for DeBruijnAnalysis {
    type Data = Data;
    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn make(egraph: &EGraph, enode: &DeBruijn) -> Data {
        let constant = eval(egraph, enode);
        Data { constant, previous_rewrites: HashSet::default() }
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
        egraph[subst[i1]].len() == 1 && egraph[subst[i1]].nodes[0].index().is_some()
        && egraph[subst[i2]].len() == 1 && egraph[subst[i2]].nodes[0].index().is_some()
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
                target_index: var("?i2"),
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
                add_pattern: "(let ?v (sub (shift ?i ?i) (shift @0 ?e1) ?e2))".parse().unwrap(),
            }
        }),
        rw!("sub-lam"; "(sub ?i ?e1 (lam ?body))" => {
            DestructiveRewrite {
                original_pattern: "(sub ?i ?e1 (lam ?body))".parse().unwrap(),
                add_pattern: "(lam (sub (shift ?i ?i) (shift @0 ?e1) ?body))".parse().unwrap(),
            }
        }),
        // shifting - this is to shift free variables when we substitute over a lambda/let/fix.
        rw!("shift";    "(shift ?i1 ?i2)"             => { ShiftIndex { min_index: var("?i1"), index: var("?i2") }} if is_both_index(var("?i1"), var("?i2"))),
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
                add_pattern: "(let (shift ?i ?v) (shift (shift ?i ?i) ?e))".parse().unwrap(),
            }
        }),
        rw!("shift-lam"; "(shift ?i (lam ?e))" => {
            DestructiveRewrite {
                original_pattern: "(shift ?i (lam ?e))".parse().unwrap(),
                add_pattern: "(lam (shift (shift ?i ?i) ?e))".parse().unwrap(),
            }
        }),
        // rw!("shift-fix"; "(shift ?i (fix ?e))" => "(fix (shift (shift ?i ?i) ?e))"),
    ]
}

// TODO: this and its applier can probably be generalized over languages L that
// implement match_enode
struct DestructiveRewrite {
    original_pattern: Pattern<DeBruijn>,
    add_pattern: Pattern<DeBruijn>,
}

impl Applier<DeBruijn, DeBruijnAnalysis> for DestructiveRewrite {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<DeBruijn, DeBruijnAnalysis>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<DeBruijn>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let memo = (rule_name, subst.clone(), self.original_pattern.ast.clone());
        if egraph[eclass].data.previous_rewrites.contains(&memo) {
            return vec!();
        }
        egraph[eclass].data.previous_rewrites.insert(memo);
        let mut ids = self.add_pattern.apply_one(egraph, eclass, subst, searcher_ast, rule_name);
        if prune_enodes_matching(egraph, &self.original_pattern.ast, subst, &eclass, rule_name) {
            ids.push(eclass);
        }
        ids
    }
}

/// Removes enodes matching the rec_expr from the egraph.
///
/// I think that we could do slightly better than a HashMap by having a mutable
/// RecExpr and storing which Ids we've visited on the nodes, but the difference
/// between passing around clones of a HashMap/HashSet everywhere and using a
/// single mutable HashMap is minimal in my testing (0.2s for a test taking 9s -
/// although this was just a single test).
fn prune_enodes_matching(egraph: &mut egg::EGraph<DeBruijn, DeBruijnAnalysis>, rec_expr: &RecExpr<ENodeOrVar<DeBruijn>>, subst: &Subst, eclass: &Id, rule_name: Symbol) -> bool {
    let dr_enabled = match rule_name.as_str() {
        "if-true" => true,
        "if-false" => true,
        "if-elim" => true,
        "beta" => false,
        "let-app" => true,
        "let-add" => true,
        "let-eq" => true,
        "let-const" => true,
        "let-if" => false,
        "let-var-same" => true,
        "let-var-diff" => true,
        "let-lam-same" => false,
        "let-lam-diff" => false,
        _ => false,
    };
    if !dr_enabled {
        return false;
    }
    let mut memo = HashMap::default();
    let rec_expr_id: Id = (rec_expr.as_ref().len() - 1).into();
    // Handles cycles - if we get back here then it matches.
    memo.insert((rec_expr_id, *eclass), true);
    let original_len = egraph[*eclass].nodes.len();

    if original_len == 1 {
        return false;
    }
    egraph[*eclass].nodes = egraph[*eclass].nodes
        .to_owned()
        .into_iter()
        .filter(|node| {
            let res = match_enode(egraph, &rec_expr, &rec_expr_id, subst, node, &mut memo);
            // if res {
            //     // println!("{} filtering node {:?}", rule_name, node)
            // }
            !res
        })
        .collect();
    original_len > egraph[*eclass].nodes.len()
}

/// This function recursively traverses the rec_expr and enode in lock step. If
/// they have matching constants, then we can simply check their equality. Most
/// of the cases, however, come from recursively checking the contained rec_expr
/// nodes against contained eclasses.
fn match_enode(egraph: &egg::EGraph<DeBruijn, DeBruijnAnalysis>, rec_expr: &RecExpr<ENodeOrVar<DeBruijn>>, rec_expr_id: &Id, subst: &Subst, enode: &DeBruijn, memo: &mut HashMap<(Id, Id), bool>) -> bool {
    match &rec_expr[*rec_expr_id] {
        ENodeOrVar::ENode(n) => {
            match (n, enode) {
                // First base cases are when leaves of the expressions match
                (DeBruijn::Bool(b_re), DeBruijn::Bool(b)) => b_re == b,
                (DeBruijn::Num(n_re), DeBruijn::Num(n)) => n_re == n,
                (DeBruijn::Index(dbi_re), DeBruijn::Index(dbi)) => dbi_re == dbi,
                // Recursive cases
                (DeBruijn::Add([n1_re, n2_re]), DeBruijn::Add([n1, n2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, n1_re, subst, n1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, n2_re, subst, n2, memo),
                (DeBruijn::App([e1_re, e2_re]), DeBruijn::App([e1, e2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, e1_re, subst, e1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e2_re, subst, e2, memo),
                (DeBruijn::Lam([body_re]), DeBruijn::Lam([body])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, body_re, subst, body, memo),
                (DeBruijn::Let([v_re, e_re]), DeBruijn::Let([v, e])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, v_re, subst, v, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e_re, subst, e, memo),
                (DeBruijn::Fix([e_re]), DeBruijn::Fix([e])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, e_re, subst, e, memo),
                (DeBruijn::If([b_re, e1_re, e2_re]), DeBruijn::If([b, e1, e2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, b_re, subst, b, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e1_re, subst, e1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e2_re, subst, e2, memo),
                (DeBruijn::Sub([dbi_re, e_re, body_re]), DeBruijn::Sub([dbi, e, body])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, dbi_re, subst, dbi, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e_re, subst, e, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, body_re, subst, body, memo),
                (DeBruijn::Shift([dbi1_re, dbi2_re]), DeBruijn::Shift([dbi1, dbi2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, dbi1_re, subst, dbi1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, dbi2_re, subst, dbi2, memo),
                _ => false
            }
        }
        // I think this is incomparable - an enode is not an eclass. Perhaps
        // they are equal if the enode is in the eclass? I kind of don't think
        // so.
        ENodeOrVar::Var(_) => false,
    }
}

/// In this case, we have a concrete AST node (ENodeOrVar::EnNode) or Var
/// (ENodeOrVar::Var) in the rec_expr that we want to compare to an entire
/// eclass. Comparing a Var to an eclass is a base case - we just check to see
/// if they're the same. Otherwise, we need to check if there is any enode in
/// the class that we can match with the concrete AST node.
fn any_enode_in_eclass_matches(egraph: &egg::EGraph<DeBruijn, DeBruijnAnalysis>, rec_expr: &RecExpr<ENodeOrVar<DeBruijn>>, rec_expr_id: &Id, subst: &Subst, eclass: &Id, memo: &mut HashMap<(Id, Id), bool>) -> bool {
    if let Some(res) = memo.get(&(*rec_expr_id, *eclass)) {
        return *res
    }
    let res = {
        // This is the second and last base case (aside from cycles) where we can
        // conclude a pattern matches.
        if let ENodeOrVar::Var(v) = rec_expr[*rec_expr_id] {
            return subst[v] == *eclass;
        }
        // If we cycle back to this node, then the pattern matches.
        memo.insert((*rec_expr_id, *eclass), true);
        egraph[*eclass].iter().any(|node| match_enode(egraph, rec_expr, &rec_expr_id, subst, node, memo))
    };
    // Update the memo since we only set it to 'true' temporarily to handle cycles.
    memo.insert((*rec_expr_id, *eclass), res);
    res
}

struct ShiftIndex {
    min_index: Var,
    index: Var,
}

// It is assumed that this Id is a singleton eclass containing only an index.
//
// The check should be done by e.g. is_both_index().
fn extract_dbi(egraph: &EGraph, index: Id) -> DeBruijnIndex {
    match egraph[index].nodes[0] {
            DeBruijn::Index(dbi) => dbi,
            _ => unreachable!(),
        }
}

/// Converts (shift i) => i + 1 for a debruijn index.
///
/// Example:
///
/// (shift @0) => @1
///
/// This is a destructive rewrite (the original shift is removed). It's unclear
/// whether doing this destructively gains anything because sharing probably
/// makes it so that there aren't a lot of these nodes (note that (shift i) is a
/// leaf).
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
        let index_dbi = extract_dbi(egraph, index_id);
        let min_dbi = extract_dbi(egraph, min_dbi_id);
        // println!("shifting index: {} min_index: {}", index_dbi, min_dbi);
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
    target_index: Var,
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
        let target_index_id = subst[self.target_index];
        let sub_index = extract_dbi(egraph, sub_index_id);
        let target_index = extract_dbi(egraph, target_index_id);
        // Remove the sub we matched.
        egraph[eclass].nodes = egraph[eclass].nodes
            .to_owned()
            .into_iter()
            .filter(|node| match node {
                DeBruijn::Sub([id1, id2, id3])
                    if *id1 == sub_index_id
                    && *id2 == sub_e_id
                    && *id3 == target_index_id => false,
                _ => true,
            })
            .collect();
        // If they're equal, substitute
        let new_expr_id = if target_index.0 == sub_index.0 {
            sub_e_id
        // If the target index is greater, then it must be free. We need to
        // decrement it.
        } else if target_index.0 > sub_index.0 {
            egraph.add(DeBruijn::Index(target_index.decrement()))
        // Otherwise, it's bound and we can't touch it.
        } else {
            egraph.add(DeBruijn::Index(target_index))
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
    dbsmallstep_compose, rules(),
    "(let
        (lam (lam (lam (app @2 (app @1 @0)))))
        (let 
            (lam (+ @0 1))
            (app (app @1 @0) @0)
        )
    )"
    =>
    // "(app (app (lam (lam (lam (app @2 (app @1 @0))))) ?x) ?x)",
    // "(app (app (lam (lam (lam (app @2 (app @1 @0))))) (lam (+ @0 1))) (lam (+ @0 1)))",
    "(lam (+ @0 2))"
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
     (let (lam (+ @0 1))
     (let (lam (app (app @2 @0) @0))
     (app @0
       @1))))"
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
        (app @0 3))"
    =>
    "2"
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
