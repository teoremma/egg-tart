use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;

use crate::benchmarks;

define_language! {
    enum Lambda {
        Num(i32),
        "var" = Var(Id),
        "+" = Add([Id; 2]),
        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),
        "let" = Let([Id; 3]),
        "map" = Map([Id; 1]),
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
}

type EGraph = egg::EGraph<Lambda, LambdaAnalysis>;

#[derive(Default)]
struct LambdaAnalysis;

#[derive(Debug)]
struct Data {
    free: HashSet<Id>,
    constant: Option<(Lambda, PatternAst<Lambda>)>,
}

fn eval(egraph: &EGraph, enode: &Lambda) -> Option<(Lambda, PatternAst<Lambda>)> {
    let x = |i: &Id| egraph[*i].data.constant.as_ref().map(|c| &c.0);
    match enode {
        Lambda::Num(n) => Some((enode.clone(), format!("{}", n).parse().unwrap())),
        Lambda::Add([a, b]) => Some((
            Lambda::Num(x(a)?.num()?.checked_add(x(b)?.num()?)?),
            format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
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
            Lambda::Lambda([v, a]) => {
                free.extend(f(a));
                free.remove(v);
            }
            _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        }
        let constant = eval(egraph, enode);
        Data { constant, free }
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
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        // subst rules
        rw!("beta";     "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rw!("let-app";  "(let ?v ?e (app ?a ?b))" => "(app (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-add";  "(let ?v ?e (+   ?a ?b))" => "(+   (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-const";
            "(let ?v ?e ?c)" => "?c" if is_const(var("?c"))),
        rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
        rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-lam-same"; "(let ?v1 ?e (lam ?v1 ?body))" => "(lam ?v1 ?body)"),
        rw!("let-lam-diff";
            "(let ?v1 ?e (lam ?v2 ?body))" =>
            { CaptureAvoid {
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(lam ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(lam ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("map-fusion";
            "(app (map ?f) (app (map ?g) ?e))" =>
            { MapFusionApplier {
                fresh: var("?fresh"), 
                fusion: "(app (map (lam ?fresh (app ?f (app ?g (var ?fresh))))) ?e)".parse().unwrap(),
            }}),
        rw!("map-fission";
            "(map (lam ?x (app ?f (app ?g (var ?x)))))"
            =>
            { MapFissionApplier {
                fresh: var("?fresh"), x: var("?x"), f: var("?f"),
                // if x is free in f, fission is not possible
                if_free: "(map (lam ?x (app ?f (app ?g (var ?x)))))".parse().unwrap(),
                if_not_free: "(lam ?fresh 
                                (app (map ?f) 
                                     (app (map (lam ?x 
                                                    (app ?g (var ?x)))) 
                                          (var ?fresh))))".parse().unwrap(),
            }}),
    ]
}

struct CaptureAvoid {
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
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = Lambda::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_free
                .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
        } else {
            self.if_not_free
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        }
    }
}

struct MapFusionApplier {
    fresh: Var,
    fusion: Pattern<Lambda>,
}

impl Applier<Lambda, LambdaAnalysis> for MapFusionApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Lambda>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let mut subst = subst.clone();
        let sym = Lambda::Symbol(format!("_{}", eclass).into());
        subst.insert(self.fresh, egraph.add(sym));
        self.fusion
            .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
    }
}

struct MapFissionApplier {
    fresh: Var,
    x: Var,
    f: Var,
    if_free: Pattern<Lambda>,
    if_not_free: Pattern<Lambda>,
}

impl Applier<Lambda, LambdaAnalysis> for MapFissionApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Lambda>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let x = subst[self.x];
        let f = subst[self.f];
        let x_free_in_f = egraph[f].data.free.contains(&x);
        if x_free_in_f {
            self.if_free
                .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
        } else {
            let mut subst = subst.clone();
            let sym = Lambda::Symbol(format!("_m{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_not_free
                .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
        }
    }
}

egg::test_fn! {
    lambda_under, rules(),
    "(lam x (+ 4
               (app (lam y (var y))
                    4)))"
    =>
    // "(lam x (+ 4 (let y 4 (var y))))",
    // "(lam x (+ 4 4))",
    "(lam x 8))",
}

egg::test_fn! {
    lambda_if_elim, rules(),
    "(if (= (var a) (var b))
         (+ (var a) (var a))
         (+ (var a) (var b)))"
    =>
    "(+ (var a) (var b))"
}

egg::test_fn! {
    lambda_let_simple, rules(),
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
    lambda_capture, rules(),
    "(let x 1 (lam x (var x)))" => "(lam x 1)"
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_capture_free, rules(),
    "(let y (+ (var x) (var x)) (lam x (var y)))" => "(lam x (+ (var x) (var x)))"
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_closure_not_seven, rules(),
    "(let five 5
     (let add-five (lam x (+ (var x) (var five)))
     (let five 6
     (app (var add-five) 1))))"
    =>
    "7"
}

egg::test_fn! {
    lambda_compose, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1)) (var add1))))"
    =>
    "(lam ?x (+ 1
                (app (lam ?y (+ 1 (var ?y)))
                     (var ?x))))",
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn! {
    lambda_if_simple, rules(),
    "(if (= 1 1) 7 9)" => "7"
}

egg::test_fn! {
    lambda_compose_many, rules(),
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

egg::test_fn! {
    lambda_compose_id, rules(),
    // "(app (app (lam f (lam g (app (var f) (var g)))) (lam x (var x))) (lam x (var x)))"
    // =>
    // "(lam ?x (var ?x))"

    "(app (app (lam f (lam g (lam x (app (var f) (app (var g) (var x)))))) (lam x (var x))) (lam x (var x)))"
    =>
    "(lam ?x (var ?x))"
    
//    "(app
//         (app 
//             (lam f (lam g (lam x (app f (app g x)))))))"
//     =>
//     "(lam ?x (var ?x))"

    // "(let f (lam x (var x)) (app (var f) (var g)))"
    // =>
    // "(app (lam ?x (var ?x)) (var g))"

    // "(app (lam f (lam g (lam x (app f (app g x))))) (lam x (var x)))"
    // =>
    // "(lam ?g (lam ?x (app ?g ?x)))"
}

egg::test_fn! {
    lambda_map_fusion, rules(),
    // "(map (var f) (map (var g) (var xs)))"
    "(app (map (var f)) (app (map (var g)) (var xs)))"
    =>
    // "(map (lam ?x (app (var f) (app (var g) (var ?x)))) (var xs))"
    "(app (map (lam ?x (app (var f) (app (var g) (var ?x))))) (var xs))"
}

egg::test_fn! {
    lambda_map_fission_not_free, rules(),
    "(map (lam x (app (var f) (app (var g) (var x)))))"
    =>
    "(lam ?y 
       (app (map (var f)) 
            (app (lam ?x (app (var g) 
                              (var ?x))) 
                 (var ?y))))"
}

#[test]
fn lambda_map_fission() {
    let start = "(map (lam x 
                        (app (var f) 
                             (app (var g) 
                                  (var x)))))".parse().unwrap();
    let goal = "(lam ?y 
                  (app (map (var f)) 
                       (app (lam ?x 
                              (app (var g) 
                                   (var ?x))) 
                            (var ?y))))".parse().unwrap();
    let runner_name = std::format!("lambda_map_fission");
    let runner = egg::Runner::default()
                    .with_iter_limit(100000)
                    .with_node_limit(1000000)
                    .with_time_limit(std::time::Duration::from_secs(30));

    benchmarks::test_runner(&runner_name, Some(runner), &rules(), start, &[goal], None, true);
}