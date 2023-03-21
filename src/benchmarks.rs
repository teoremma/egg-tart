use egg::*;
use std::{fmt::Display, fs::File, io::Write, path::PathBuf};

pub fn env_var<T>(s: &str) -> Option<T>
where
    T: std::str::FromStr,
    T::Err: std::fmt::Debug,
{
    use std::env::VarError;
    match std::env::var(s) {
        Err(VarError::NotPresent) => None,
        Err(VarError::NotUnicode(_)) => panic!("Environment variable {} isn't unicode", s),
        Ok(v) if v.is_empty() => None,
        Ok(v) => match v.parse() {
            Ok(v) => Some(v),
            Err(err) => panic!("Couldn't parse environment variable {}={}, {:?}", s, v, err),
        },
    }
}

pub fn test_runner<L, A>(
    name: &str,
    runner: Option<Runner<L, A, ()>>,
    rules: &[Rewrite<L, A>],
    start: RecExpr<L>,
    goals: &[Pattern<L>],
    check_fn: Option<fn(Runner<L, A, ()>)>,
    should_check: bool,
) where
    L: Language + Display + FromOp + 'static,
    A: Analysis<L> + Default,
{
    let mut runner = runner.unwrap_or_default();

    if let Some(lim) = env_var("EGG_NODE_LIMIT") {
        runner = runner.with_node_limit(lim)
    }
    if let Some(lim) = env_var("EGG_ITER_LIMIT") {
        runner = runner.with_iter_limit(lim)
    }
    if let Some(lim) = env_var("EGG_TIME_LIMIT") {
        runner = runner.with_time_limit(std::time::Duration::from_secs(lim))
    }

    runner = runner.with_expr(&start);
    // NOTE this is a bit of hack, we rely on the fact that the
    // initial root is the last expr added by the runner. We can't
    // use egraph.find_expr(start) because it may have been pruned
    // away
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    if true {
        let goals = goals.to_vec();
        runner = runner.with_hook(move |r| {
            if goals
                .iter()
                .all(|g: &Pattern<_>| g.search_eclass(&r.egraph, id).is_some())
            {
                Err("Proved all goals".into())
            } else {
                Ok(())
            }
        });
    }
    let mut runner = runner.run(rules);

    let report = runner.report();
    eprintln!("{report}");
    println!("{name},{stop_reason:?},{nodes},{classes},{memo},{time},{its},{rebuilds}",
        stop_reason=report.stop_reason,
        nodes=report.egraph_nodes,
        classes=report.egraph_classes,
        memo=report.memo_size,
        time=report.total_time,
        its=report.iterations,
        rebuilds=report.rebuilds);
}

pub fn fibonacci(n: usize) -> usize {
    let (mut a, mut b) = (0, 1);
    if n == 0 { return a }
    for _ in 1..n {
        b += a;
        a = b - a;
    }
    b
}

pub fn fib_sexprs(n: usize) -> (String, String) {
    let start = 
    std::format!("(let fib (fix fib (lam n
        (if (= (var n) 0)
            0
        (if (= (var n) 1)
            1
        (+ (app (var fib)
                (+ (var n) -1))
            (app (var fib)
                (+ (var n) -2)))))))
        (app (var fib) {n}))");
    let goal = std::format!("{tgt}", tgt=fibonacci(n));
    (start, goal)
}

pub fn double_many_inside_sexprs(n: usize) -> (String, String) {
    fn double_add(n: usize) -> String {
        if n == 0 { "(var add1)".to_string() }
        else { std::format!("(app (var double) {})", double_add(n - 1)) }
    }
    let start = std::format!("(let compose (lam f (lam g (lam x (app (var f)
                                                   (app (var g) (var x))))))
                 (let double (lam f (app (app (var compose) (var f)) (var f)))
                 (let add1 (lam y (+ (var y) 1)) {} )))", double_add(n));
    let goal = std::format!("(lam ?x (+ (var ?x) {}))", usize::pow(2, n as u32));
    (start, goal)
}

pub fn double_many_outside_sexprs(n: usize) -> (String, String) {
    fn app_double(n: usize) -> String {
        if n == 0 { panic!("Shouldn't be zero") }
        else if n == 1 { "(var double)".to_string() }
        else {std::format!("(app (var double) {})", app_double(n - 1))}
    }
    let start = std::format!("(let compose (lam f (lam g (lam x (app (var f)
                                                   (app (var g) (var x))))))
                 (let double (lam f (app (app (var compose) (var f)) (var f)))
                 (let add1 (lam y (+ (var y) 1)) (app {} (var add1)) )))", app_double(n));
    let goal = std::format!("(lam ?x (+ (var ?x) {}))", usize::pow(2, n as u32));
    (start, goal)
}

pub fn add_many_sexprs(n: usize) -> (String, String) {
    fn comp_add1(n: usize) -> String {
        if n == 0 { panic!("Shouldn't be zero") }
        else if n == 1 { "(var add1)".to_string() }
        else { std::format!("(app (app (var comp) (var add1)) {})", comp_add1(n - 1)) }
    }
    let start = std::format!("(let comp (lam f (lam g (lam x (app (var f)
                                                   (app (var g) (var x))))))
                 (let add1 (lam y (+ (var y) 1)) {} ))", comp_add1(n));
    let goal = std::format!("(lam ?x (+ (var ?x) {}))", n);
    (start, goal)
}