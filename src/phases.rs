use std::vec;

use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;

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
        // sub is equivalent to let, but used only for intermediate steps
        "sub" = Sub([Id; 3]),

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

    fn is_sub(&self) -> bool {
        if let Lambda::Sub(_) = self { true }
        else { false }
    }
}

type EGraph = egg::EGraph<Lambda, LambdaAnalysis>;

#[derive(Default, Clone)]
struct LambdaAnalysis;

#[derive(Debug, Clone)]
struct Data {
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


fn main_rules() -> Vec<Rewrite<Lambda, LambdaAnalysis>> {
    vec![
        rw!("if-true";  "(if  true ?then ?else)" => "?then"),
        rw!("if-false"; "(if false ?then ?else)" => "?else"),
        rw!("if-elim"; "(if (= (var ?x) ?e) ?then ?else)" => "?else"
            if ConditionEqual::parse("(let ?x ?e ?then)", "(let ?x ?e ?else)")),
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),

        // TODO: compare rewriting fix to let or sub
        // rw!("fix";      "(fix ?v ?e)"             => "(sub ?v (fix ?v ?e) ?e)"),
        rw!("fix";      "(fix ?v ?e)"             => "(let ?v (fix ?v ?e) ?e)"),
        rw!("beta";     "(app (lam ?v ?body) ?e)" => "(sub ?v ?e ?body)"),

        // let rules introduce sub now
        rw!("let"; "(let ?v ?e ?body)" => "(sub ?v ?e ?body)"),
    ]
}

fn subst_rules() -> Vec<Rewrite<Lambda, LambdaAnalysis>> {
   vec![
        rw!("sub-app";  "(sub ?v ?e (app ?a ?b))" => "(app (sub ?v ?e ?a) (sub ?v ?e ?b))"),
        rw!("sub-add";  "(sub ?v ?e (+   ?a ?b))" => "(+   (sub ?v ?e ?a) (sub ?v ?e ?b))"),
        rw!("sub-eq";   "(sub ?v ?e (=   ?a ?b))" => "(=   (sub ?v ?e ?a) (sub ?v ?e ?b))"),
        rw!("sub-const";
            "(sub ?v ?e ?c)" => "?c" if is_const(var("?c"))),
        rw!("sub-if";
            "(sub ?v ?e (if ?cond ?then ?else))" =>
            "(if (sub ?v ?e ?cond) (sub ?v ?e ?then) (sub ?v ?e ?else))"
        ),
        rw!("sub-var-same"; "(sub ?v1 ?e (var ?v1))" => "?e"),
        rw!("sub-var-diff"; "(sub ?v1 ?e (var ?v2))" => "(var ?v2)"
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("sub-lam-same"; "(sub ?v1 ?e (lam ?v1 ?body))" => "(lam ?v1 ?body)"),
        rw!("sub-lam-diff";
            "(sub ?v1 ?e (lam ?v2 ?body))" =>
            { CaptureAvoid {
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(lam ?v2 (sub ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(lam ?fresh (sub ?v1 ?e (sub ?v2 (var ?fresh) ?body)))".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
   ] 
}

// Returns a new runner with goal checking for a given eclass
fn runner_with_goals(eclass: Id, goals: Vec<Pattern<Lambda>>) -> Runner<Lambda, LambdaAnalysis> {
    let node_limit = 1000000;
    let iter_limit = 10000;
    let time_limit = 10;

    let mut runner = Runner::default()
        .with_node_limit(node_limit)
        .with_iter_limit(iter_limit)
        .with_time_limit(std::time::Duration::from_secs(time_limit));
    runner = runner.with_hook(move |r| {
        if goals
            .iter()
            .all(|g: &Pattern<_>| g.search_eclass(&r.egraph, eclass).is_some())
        {
            Err("Proved all goals".into())
        } else {
            Ok(())
        }
    });
    runner
}
// basically a reimplementation of egg::test::test_runner
fn test_phased_runners(
    start: RecExpr<Lambda>,
    goals: &[Pattern<Lambda>]
) {

    let mut egraph = EGraph::new(LambdaAnalysis);
    let root_id = egraph.add_expr(&start);
    let root_id = egraph.find(root_id);
    let goals_vec = goals.to_vec();

    // alternate between main and subst runners
    loop {
        println!("Running main runner");
        let mut main_runner = runner_with_goals(root_id , goals_vec.clone());
        main_runner = main_runner.with_egraph(egraph.clone()).run(&main_rules());
        println!("{report}", report = main_runner.report());
        if let StopReason::Other(_) = main_runner.stop_reason.unwrap() { break }
        egraph = main_runner.egraph;
        let (_, best) = Extractor::new(&egraph, AstSize).find_best(root_id);
        println!("Best so far: {}", best.pretty(80));
        
        println!("Running subst runner");
        let mut subst_runner = runner_with_goals(root_id , goals_vec.clone());
        subst_runner = subst_runner.with_egraph(egraph.clone()).run(&subst_rules());
        println!("{report}", report = subst_runner.report());
        if let StopReason::Other(_) = subst_runner.stop_reason.unwrap() { break }
        egraph = subst_runner.egraph;
        let (_, best) = Extractor::new(&egraph, AstSize).find_best(root_id);
        println!("Best so far: {}", best.pretty(80));

        for eclass in egraph.classes_mut() {
            // ugly af :|
            let filtered_enodes: Vec<Lambda> = eclass.nodes.clone().into_iter().filter(|node| !node.is_sub()).collect();
            if !filtered_enodes.is_empty() {
                eclass.nodes = filtered_enodes;
            }
        }
    }

    // Alternate between main_runner and sub_runner, deleting sub enodes in the process
}

macro_rules! phased_test_fn {
    (
        $name:ident,
        $start:literal
        =>
        $($goal:literal),+ $(,)?
    ) => {
    #[test]
    pub fn $name() {
        test_phased_runners(
            $start.parse().unwrap(),
            &[$( $goal.parse().unwrap() ),+],
        )
    }
    };
}

phased_test_fn! {
    phased_lambda_under,
    "(lam x (+ 4
               (app (lam y (var y))
                    4)))"
    =>
    "(lam x 8))"
}

phased_test_fn! {
    phased_lambda_if_elim,
    "(if (= (var a) (var b))
         (+ (var a) (var a))
         (+ (var a) (var b)))"
    =>
    "(+ (var a) (var b))"
}

phased_test_fn! {
    phased_lambda_let_simple,
    "(let x 0
     (let y 1
     (+ (var x) (var y))))"
    =>
    // "(let ?a 0
    //  (+ (var ?a) 1))",
    // "(+ 0 1)",
    "1",
}

phased_test_fn! {
    phased_lambda_compose,
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

phased_test_fn! {
    phased_lambda_if_simple,
    "(if (= 1 1) 7 9)" => "7"
}

phased_test_fn! {
    phased_lambda_compose_many,
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

phased_test_fn! {
    phased_lambda_function_repeat,
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
}

phased_test_fn! {
    phased_lambda_if,
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

phased_test_fn! {
    phased_lambda_fib,
    "(let fib (fix fib (lam n
        (if (= (var n) 0)
            0
        (if (= (var n) 1)
            1
        (+ (app (var fib)
                (+ (var n) -1))
            (app (var fib)
                (+ (var n) -2)))))))
        (app (var fib) 4))"
    => "3"
}

// Times out with 8 doubles
// (with 7 doubles, takes ~20s)
// (sketch guided takes ~90s with 4 doubles)
phased_test_fn! {
    lambda_phased_compose_many_many_1,
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
    "(lam ?x (+ (var ?x) 512))"
}

// failing for some reason
phased_test_fn! {
    phased_lambda_constant_fold,
    "(lam x (+ 1 (+ 1 (var x))))"
    =>
    "(lam ?x (+ 1 (let x (var ?x) (+ 1 (var ?x)))))"
}
