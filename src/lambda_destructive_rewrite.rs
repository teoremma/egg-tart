use egg::{rewrite as rw, *, test::test_runner};
use fxhash::FxHashSet as HashSet;
use fxhash::FxHashMap as HashMap;
use crate::benchmarks;

define_language! {
    enum Lambda {
        Bool(bool),
        Num(i32),

        "var" = Var(Id),

        "+" = Add([Id; 2]),
        "=" = Eq([Id; 2]),

        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),
        "let" = Let([Id; 3]),
        "fix" = Fix([Id; 2]),

        "if" = If([Id; 3]),

        Symbol(egg::Symbol),
    }
}

impl Lambda {
    fn num(&self) -> Option<i32> {
        match self {
            Lambda::Num(n) => Some(*n),
            _ => None,
        }
    }

    fn increment_id(&self, increment: usize) -> Self {
        match self {
            Lambda::Var(id) => Lambda::Var(increment_id(*id, increment)),
            Lambda::Add([id1, id2]) => Lambda::Add([increment_id(*id1, increment), increment_id(*id2, increment)]),
            Lambda::Eq([id1, id2]) => Lambda::Eq([increment_id(*id1, increment), increment_id(*id2, increment)]),
            Lambda::App([id1, id2]) => Lambda::App([increment_id(*id1, increment), increment_id(*id2, increment)]),
            Lambda::Lambda([id1, id2]) => Lambda::Lambda([increment_id(*id1, increment), increment_id(*id2, increment)]),
            Lambda::Let([id1, id2, id3]) =>
                Lambda::Let([increment_id(*id1, increment), increment_id(*id2, increment), increment_id(*id3, increment)]),
            Lambda::Fix([id1, id2]) => Lambda::Fix([increment_id(*id1, increment), increment_id(*id2, increment)]),
            Lambda::If([id1, id2, id3]) =>
                Lambda::If([increment_id(*id1, increment), increment_id(*id2, increment), increment_id(*id3, increment)]),
            Lambda::Bool(_) | Lambda::Num(_) | Lambda::Symbol(_) => self.to_owned()
        }
    }
}

fn increment_id(id: Id, increment: usize) -> Id {
    let id_as_usize: usize = id.into();
    (id_as_usize + increment).into()
}

type EGraph = egg::EGraph<Lambda, LambdaAnalysis>;

#[derive(Default)]
struct LambdaAnalysis;

#[derive(Clone, Debug)]
struct Data {
    previous_rewrites: HashSet<(Symbol, Subst, PatternAst<Lambda>)>,
    free: HashSet<Id>,
    constant: Option<(Lambda, PatternAst<Lambda>)>,
}

fn eval(egraph: &EGraph, enode: &Lambda) -> Option<(Lambda, PatternAst<Lambda>)> {
    let x = |i: &Id| egraph[*i].data.constant.as_ref().map(|c| &c.0);
    match enode {
        Lambda::Num(n) => Some((enode.clone(), format!("{}", n).parse().unwrap())),
        Lambda::Bool(b) => Some((enode.clone(), format!("{}", b).parse().unwrap())),
        Lambda::Add([a, b]) => Some((
            Lambda::Num(x(a)?.num()? + x(b)?.num()?),
            format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        Lambda::Eq([a, b]) => Some((
            Lambda::Bool(x(a)? == x(b)?),
            format!("(= {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        _ => None,
    }
}

impl Analysis<Lambda> for LambdaAnalysis {
    type Data = Data;
    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        let before_len = to.free.len();
        // to.free.extend(from.free);
        to.free.retain(|i| from.free.contains(i));
        // compare lengths to see if I changed to or from
        DidMerge(
            before_len != to.free.len(),
            to.free.len() != from.free.len(),
        ) | merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn make(egraph: &EGraph, enode: &Lambda) -> Data {
        let f = |i: &Id| egraph[*i].data.free.iter().cloned();
        let mut free = HashSet::default();
        match enode {
            Lambda::Var(v) => {
                free.insert(*v);
            }
            Lambda::Let([v, a, b]) => {
                free.extend(f(b));
                free.remove(v);
                free.extend(f(a));
            }
            Lambda::Lambda([v, a]) | Lambda::Fix([v, a]) => {
                free.extend(f(a));
                free.remove(v);
            }
            _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        }
        let constant = eval(egraph, enode);
        Data { constant, free, previous_rewrites: HashSet::default() }
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

fn rules() -> Vec<Rewrite<Lambda, LambdaAnalysis>> {
    vec![
        // open term rules
        //   not destructive
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
        //   destructive
        rw!("if-true";  "(if  true ?then ?else)" => {
            DestructiveRewrite {
                original_pattern: "(if  true ?then ?else)".parse().unwrap(),
                add_pattern: "?then".parse().unwrap(),
            }
        }),
        rw!("if-false"; "(if false ?then ?else)" => {
            DestructiveRewrite {
                original_pattern: "(if false ?then ?else)".parse().unwrap(),
                add_pattern: "?else".parse().unwrap(),
            }
        }),
        rw!("if-elim"; "(if (= (var ?x) ?e) ?then ?else)" => {
            DestructiveRewrite {
                original_pattern: "(if (= (var ?x) ?e) ?then ?else)".parse().unwrap(),
                add_pattern: "?else".parse().unwrap(),
            }}
            if ConditionEqual::parse("(let ?x ?e ?then)", "(let ?x ?e ?else)")
        ),
        // subst rules
        //   not destructive
        rw!("fix";      "(fix ?v ?e)"             => "(let ?v (fix ?v ?e) ?e)"),
        //   destructive
        rw!("beta";     "(app (lam ?v ?body) ?e)" => {
            DestructiveRewrite {
                original_pattern: "(app (lam ?v ?body) ?e)".parse().unwrap(),
                add_pattern: "(let ?v ?e ?body)".parse().unwrap(),
            }
        }),
        rw!("let-app";  "(let ?v ?e (app ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(let ?v ?e (app ?a ?b))".parse().unwrap(),
                add_pattern: "(app (let ?v ?e ?a) (let ?v ?e ?b))".parse().unwrap(),
            }
        }),
        rw!("let-add";  "(let ?v ?e (+   ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(let ?v ?e (+   ?a ?b))".parse().unwrap(),
                add_pattern: "(+   (let ?v ?e ?a) (let ?v ?e ?b))".parse().unwrap(),
            }
        }),
        rw!("let-eq";   "(let ?v ?e (=   ?a ?b))" => {
            DestructiveRewrite {
                original_pattern: "(let ?v ?e (=   ?a ?b))".parse().unwrap(),
                add_pattern: "(=   (let ?v ?e ?a) (let ?v ?e ?b))".parse().unwrap(),
            }
        }),
        rw!("let-const";
            "(let ?v ?e ?c)" => {
            DestructiveRewrite {
                original_pattern: "(let ?v ?e ?c)".parse().unwrap(),
                add_pattern: "?c".parse().unwrap(),
            }}
            if is_const(var("?c"))),
        rw!("let-if";
            "(let ?v ?e (if ?cond ?then ?else))" => {
                DestructiveRewrite {
                    original_pattern: "(let ?v ?e (if ?cond ?then ?else))".parse().unwrap(),
                    add_pattern: "(if (let ?v ?e ?cond) (let ?v ?e ?then) (let ?v ?e ?else))".parse().unwrap(),
                }
            }
        ),
        rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => {
            DestructiveRewrite {
                original_pattern: "(let ?v1 ?e (var ?v1))".parse().unwrap(),
                add_pattern: "?e".parse().unwrap(),
            }
        }),
        rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => {
            DestructiveRewrite {
                original_pattern: "(let ?v1 ?e (var ?v2))".parse().unwrap(),
                add_pattern: "(var ?v2)".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-lam-same"; "(let ?v1 ?e (lam ?v1 ?body))" => {
            DestructiveRewrite {
                original_pattern: "(let ?v1 ?e (lam ?v1 ?body))".parse().unwrap(),
                add_pattern: "(lam ?v1 ?body)".parse().unwrap(),
            }
        }),
        rw!("let-lam-diff";
            "(let ?v1 ?e (lam ?v2 ?body))" =>
            { CaptureAvoid {
                original_pattern: "(let ?v1 ?e (lam ?v2 ?body))".parse().unwrap(),
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(lam ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(lam ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
    ]
}

// TODO: this and its applier can probably be generalized over languages L that
// implement match_enode
struct DestructiveRewrite {
    original_pattern: Pattern<Lambda>,
    add_pattern: Pattern<Lambda>,
}

impl Applier<Lambda, LambdaAnalysis> for DestructiveRewrite {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Lambda, LambdaAnalysis>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Lambda>>,
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
fn prune_enodes_matching(egraph: &mut egg::EGraph<Lambda, LambdaAnalysis>, rec_expr: &RecExpr<ENodeOrVar<Lambda>>, subst: &Subst, eclass: &Id, rule_name: Symbol) -> bool {
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
fn match_enode(egraph: &egg::EGraph<Lambda, LambdaAnalysis>, rec_expr: &RecExpr<ENodeOrVar<Lambda>>, rec_expr_id: &Id, subst: &Subst, enode: &Lambda, memo: &mut HashMap<(Id, Id), bool>) -> bool {
    match &rec_expr[*rec_expr_id] {
        ENodeOrVar::ENode(n) => {
            match (n, enode) {
                // First base cases are when leaves of the expressions match
                (Lambda::Bool(b_re), Lambda::Bool(b)) => b_re == b,
                (Lambda::Num(n_re), Lambda::Num(n)) => n_re == n,
                (Lambda::Symbol(s_re), Lambda::Symbol(s)) => s_re == s,
                // Recursive cases
                (Lambda::Var(v_re), Lambda::Var(v)) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, v_re, subst, v, memo),
                (Lambda::Add([n1_re, n2_re]), Lambda::Add([n1, n2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, n1_re, subst, n1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, n2_re, subst, n2, memo),
                (Lambda::App([e1_re, e2_re]), Lambda::App([e1, e2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, e1_re, subst, e1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e2_re, subst, e2, memo),
                (Lambda::Lambda([x_re, body_re]), Lambda::Lambda([x, body])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, x_re, subst, x, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, body_re, subst, body, memo),
                (Lambda::Let([x_re, v_re, e_re]), Lambda::Let([x, v, e])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, x_re, subst, x, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, v_re, subst, v, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e_re, subst, e, memo),
                (Lambda::Fix([e1_re, e2_re]), Lambda::Fix([e1, e2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, e1_re, subst, e1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e2_re, subst, e2, memo),
                (Lambda::If([b_re, e1_re, e2_re]), Lambda::If([b, e1, e2])) =>
                    any_enode_in_eclass_matches(egraph, rec_expr, b_re, subst, b, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e1_re, subst, e1, memo)
                    && any_enode_in_eclass_matches(egraph, rec_expr, e2_re, subst, e2, memo),
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
fn any_enode_in_eclass_matches(egraph: &egg::EGraph<Lambda, LambdaAnalysis>, rec_expr: &RecExpr<ENodeOrVar<Lambda>>, rec_expr_id: &Id, subst: &Subst, eclass: &Id, memo: &mut HashMap<(Id, Id), bool>) -> bool {
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

struct CaptureAvoid {
    original_pattern: Pattern<Lambda>,
    fresh: Var,
    v2: Var,
    e: Var,
    if_not_free: Pattern<Lambda>,
    if_free: Pattern<Lambda>,
}

impl Applier<Lambda, LambdaAnalysis> for CaptureAvoid {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Lambda>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let e = subst[self.e];
        let v2 = subst[self.v2];
        let v2_free_in_e = egraph[e].data.free.contains(&v2);
        let mut ids = if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = Lambda::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_free
                .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
        } else {
            self.if_not_free
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        };
        if prune_enodes_matching(egraph, &self.original_pattern.ast, subst, &eclass, rule_name) {
            ids.push(eclass);
        }
        ids
    }
}

egg::test_fn! {
    lambda_dr_under, rules(),
    "(lam x (+ 4
               (app (lam y (var y))
                    4)))"
    =>
    // "(lam x (+ 4 (let y 4 (var y))))",
    // "(lam x (+ 4 4))",
    "(lam x 8))",
}

egg::test_fn! {
    lambda_dr_if_elim, rules(),
    "(if (= (var a) (var b))
         (+ (var a) (var a))
         (+ (var a) (var b)))"
    =>
    "(+ (var a) (var b))"
}

egg::test_fn! {
    lambda_dr_let_simple, rules(),
    "(let x 0
     (let y 1
     (+ (var x) (var y))))"
    =>
    // "(let ?a 0
    //  (+ (var ?a) 1))",
    // "(+ 0 1)",
    "1",
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_dr_capture, rules(),
    "(let x 1 (lam x (var x)))" => "(lam x 1)"
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_dr_capture_free, rules(),
    "(let y (+ (var x) (var x)) (lam x (var y)))" => "(lam x (+ (var x) (var x)))"
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_dr_closure_not_seven, rules(),
    "(let five 5
     (let add-five (lam x (+ (var x) (var five)))
     (let five 6
     (app (var add-five) 1))))"
    =>
    "7"
}

egg::test_fn! {
    lambda_dr_compose, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1)) (var add1))))"
    =>
    // Can't have this because it won't be equivalent
    // "(lam ?x (+ 1
    //             (app (lam ?y (+ 1 (var ?y)))
    //                  (var ?x))))",
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn! {
    lambda_dr_if_simple, rules(),
    "(if (= 1 1) 7 9)" => "7"
}

egg::test_fn! {
    lambda_dr_compose_many, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1))
          (app (app (var compose) (var add1))
               (app (app (var compose) (var add1))
                    (app (app (var compose) (var add1))
                         (app (app (var compose) (var add1))
                              (app (app (var compose) (var add1))
                                   (var add1)))))))))"
    =>
    "(lam ?x (+ (var ?x) 7))"
}

// Times out with 8 doubles
// (with 7 doubles, takes ~20s)
// (sketch guided takes ~90s with 4 doubles)
egg::test_fn! {
    lambda_dr_compose_many_many_1, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let double (lam f (app (app (var compose) (var f)) (var f)))
     (let add1 (lam y (+ (var y) 1))
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
         (var add1)))))))))))))"
    =>
    "(lam ?x (+ (var ?x) 256))"
}

// 8 doubles times out for CallByName
// 7 doubles takes ~20s
// SketchGuided can handle many_many_2 but not this one...
//   might be a faulty implementation
// small step semantics takes >120s for 7
egg::test_fn! {
    lambda_dr_compose_many_many_1_no_let, rules(),
    "(app (app
     (lam double
     (lam add1
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
     (app (var double)
         (var add1))))))))))
(lam f (app (app (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x)))))) (var f)) (var f)))) (lam y (+ (var y) 1)))"
    =>
    "(lam ?x (+ (var ?x) 128))"
}

egg::test_fn! {
    lambda_dr_compose_many_many_2_no_let, rules(),
    "(app (app
     (lam double
     (lam add1
     (app (var double)
     (app (var double)
     (app (var double)
         (var add1))))))
(lam f (app (app (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x)))))) (var f)) (var f)))) (lam y (+ (var y) 1)))"
    =>
    "(lam ?x (+ (var ?x) 8))"
}


// Times out with 5 doubles
// (with 4 doubles, takes ~20s)
// (sketch guided runs for >90s with 3 doubles)
egg::test_fn! {
    lambda_dr_compose_many_many_2, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let double (lam f (app (app (var compose) (var f)) (var f)))
     (let add1 (lam y (+ (var y) 1))
     (app
         (app (var double)
         (app (var double)
         (app (var double)
         (app (var double)
              (var double)))))
         (var add1)))))"
    =>
    "(lam ?x (+ (var ?x) 32))"
}

egg::test_fn! {
    lambda_dr_call_by_name_1, rules(),
    "(let double (lam f (lam x (app (var f) (app (var f) (var x)))))
     (let add1 (lam y (+ (var y) 1))
     (app (var double)
         (var add1))))"
    =>
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn! {
    lambda_dr_call_by_name_2, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let double (lam f (app (app (var compose) (var f)) (var f)))
     (let add1 (lam y (+ (var y) 1))
     (app (var double)
         (var add1)))))"
    =>
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn! {
    lambda_dr_call_by_name_3, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let double (lam f (app (app (var compose) (var f)) (var f)))
     (let add1 (lam y (+ (var y) 1))
     (app
         (app (var double)
              (var double))
         (var add1)))))"
    =>
    "(lam ?x (+ (var ?x) 4))"
}

egg::test_fn! {
    lambda_dr_call_by_name_4, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (let addadd1 (lam f (app (app (var compose) (var add1)) (var f)))
     (app (var addadd1)
     (app (var addadd1)
         (var add1))))))"
    =>
    "(lam ?x (+ (var ?x) 3))"
}

egg::test_fn! {
    lambda_dr_function_repeat, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_node_limit(150_000)
        .with_iter_limit(60),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let repeat (fix repeat (lam fun (lam n
        (if (= (var n) 0)
            (lam i (var i))
            (app (app (var compose) (var fun))
                 (app (app (var repeat)
                           (var fun))
                      (+ (var n) -1)))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var repeat)
               (var add1))
          2))))"
    =>
    "(lam ?x (+ (var ?x) 2))",
    "(lam ?x (+ 1 (let x (var ?x) (+ 1 (var ?x)))))"
}

egg::test_fn! {
    lambda_dr_function_repeat_end, rules(),
    "(lam x (+ 1 (let x (var x) (+ 1 (var x)))))"
    =>
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn! {
    lambda_dr_if, rules(),
    "(let zeroone (lam x
        (if (= (var x) 0)
            0
            1))
        (+ (app (var zeroone) 0)
        (app (var zeroone) 10)))"
    =>
    // "(+ (if false 0 1) (if true 0 1))",
    // "(+ 1 0)",
    "1",
}

egg::test_fn! {
    lambda_dr_fib, rules(),
    // runner = Runner::default()
    //     .with_iter_limit(60)
    //     .with_node_limit(500_000),
    "(let fib (fix fib (lam n
        (if (= (var n) 0)
            0
        (if (= (var n) 1)
            1
        (+ (app (var fib)
                (+ (var n) -1))
            (app (var fib)
                (+ (var n) -2)))))))
        (app (var fib) 17))"
    => "1597"
}

#[test]
fn lambda_dr_fib_range() {
    let range = 0..30;
    for n in range {
        let (start, goal) = benchmarks::fib_sexprs(n);
        let start = start.parse().unwrap();
        let goal = goal.parse().unwrap();
        let runner_name = std::format!("lambda_dr_fib_{n}");
        eprintln!("####### {}", runner_name);

        benchmarks::test_runner(&runner_name, None, &rules(), start, &[goal], None, true);
        eprintln!("\n\n\n")
    }
}

#[test]
fn lambda_dr_double_many_inside_range() {
    let range = 0..10;
    for n in range {
        let (start, goal) = benchmarks::double_many_inside_sexprs(n);
        let start = start.parse().unwrap();
        let goal = goal.parse().unwrap();
        let runner_name = std::format!("lambda_dr_double_many_inside_{n}");
        eprintln!("####### {}", runner_name);

        benchmarks::test_runner(&runner_name, None, &rules(), start, &[goal], None, true);
        eprintln!("\n\n\n")
    }
}

#[test]
fn lambda_dr_double_many_outside_range() {
    let range = 1..10;
    for n in range {
        let (start, goal) = benchmarks::double_many_outside_sexprs(n);
        let start = start.parse().unwrap();
        let goal = goal.parse().unwrap();
        let runner_name = std::format!("lambda_dr_double_many_outside_{n}");
        eprintln!("####### {}", runner_name);

        benchmarks::test_runner(&runner_name, None, &rules(), start, &[goal], None, true);
        eprintln!("\n\n\n")
    }
}


#[test]
fn lambda_dr_add_many_range() {
    let range = 150..250;
    for n in range {
        let (start, goal) = benchmarks::add_many_sexprs(n);
        let start = start.parse().unwrap();
        let goal = goal.parse().unwrap();
        let runner_name = std::format!("lambda_dr_add_many_{n}");
        eprintln!("####### {}", runner_name);

        benchmarks::test_runner(&runner_name, None, &rules(), start, &[goal], None, true);
        eprintln!("\n\n\n")
    }
}

#[test]
fn lambda_dr_ematching_bench() {
    let exprs = &[
        "(let zeroone (lam x
            (if (= (var x) 0)
                0
                1))
            (+ (app (var zeroone) 0)
            (app (var zeroone) 10)))",
        "(let compose (lam f (lam g (lam x (app (var f)
                                        (app (var g) (var x))))))
        (let repeat (fix repeat (lam fun (lam n
            (if (= (var n) 0)
                (lam i (var i))
                (app (app (var compose) (var fun))
                    (app (app (var repeat)
                            (var fun))
                        (+ (var n) -1)))))))
        (let add1 (lam y (+ (var y) 1))
        (app (app (var repeat)
                (var add1))
            2))))",
        "(let fib (fix fib (lam n
            (if (= (var n) 0)
                0
            (if (= (var n) 1)
                1
            (+ (app (var fib)
                    (+ (var n) -1))
                (app (var fib)
                    (+ (var n) -2)))))))
            (app (var fib) 4))",
    ];

    let extra_patterns = &[
        "(if (= (var ?x) ?e) ?then ?else)",
        "(+ (+ ?a ?b) ?c)",
        "(let ?v (fix ?v ?e) ?e)",
        "(app (lam ?v ?body) ?e)",
        "(let ?v ?e (app ?a ?b))",
        "(app (let ?v ?e ?a) (let ?v ?e ?b))",
        "(let ?v ?e (+   ?a ?b))",
        "(+   (let ?v ?e ?a) (let ?v ?e ?b))",
        "(let ?v ?e (=   ?a ?b))",
        "(=   (let ?v ?e ?a) (let ?v ?e ?b))",
        "(let ?v ?e (if ?cond ?then ?else))",
        "(if (let ?v ?e ?cond) (let ?v ?e ?then) (let ?v ?e ?else))",
        "(let ?v1 ?e (var ?v1))",
        "(let ?v1 ?e (var ?v2))",
        "(let ?v1 ?e (lam ?v1 ?body))",
        "(let ?v1 ?e (lam ?v2 ?body))",
        "(lam ?v2 (let ?v1 ?e ?body))",
        "(lam ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))",
    ];

    egg::test::bench_egraph("lambda", rules(), exprs, extra_patterns);
}
