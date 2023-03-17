use std::fmt::Display;
use std::str::FromStr;

use egg::{rewrite as rw, *};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct DeBruijnIndex(u32);

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

        "app" = App([Id; 2]),
        "lam" = Lam([Id; 1]),
        "let" = Let([Id; 2]),
        "if" = If([Id; 3]),

        "shift" = Shift([Id; 1]),

        Index(DeBruijnIndex),
    }
}

impl DeBruijn {
    fn num(&self) -> Option<i32> {
        match self {
            DeBruijn::Num(n) => Some(*n),
            _ => None,
        }
    }
}

type EGraph = egg::EGraph<DeBruijn, DeBruijnAnalysis>;

#[derive(Default)]
struct DeBruijnAnalysis;

#[derive(Debug)]
struct Data {
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
        // let before_len = to.free.len();
        // to.free.extend(from.free);
        // to.free.retain(|i| from.free.contains(i));
        // // compare lengths to see if I changed to or from
        // DidMerge(
        //     before_len != to.free.len(),
        //     to.free.len() != from.free.len(),
        // ) |

        merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn make(egraph: &EGraph, enode: &DeBruijn) -> Data {
        // let f = |i: &Id| egraph[*i].data.free.iter().cloned();
        // let mut free = HashSet::default();
        // match enode {
        //     DeBruijn::Let([a, b]) => {
        //         free.extend(f(b));
        //         free.extend(f(a));
        //     }
        //     DeBruijn::Lam([a]) => {
        //         free.extend(f(a));
        //     }
        //     _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        // }
        let constant = eval(egraph, enode);
        Data { constant }
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

fn is_const(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    println!("is_const({:?})", v);
    move |egraph, _, subst| egraph[subst[v]].data.constant.is_some()
}

// fn inletif() -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
//     println!("inletif");
//     move |_, _, _| true
// }

fn rules() -> Vec<Rewrite<DeBruijn, DeBruijnAnalysis>> {
    vec![
        // open term rules
        rw!("if-true";  "(if true ?then ?else)" => "?then"),
        rw!("if-false"; "(if false ?then ?else)" => "?else"),
        // rw!("if-elim"; "(if (= (var ?x) ?e) ?then ?else)" => "?else"
        //     if ConditionEqual::parse("(let ?x ?e ?then)", "(let ?x ?e ?else)")),
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
        // subst rules
        // rw!("fix";      "(fix ?v ?e)"             => "(let (fix ?v ?e) ?e)"),
        // rw!("beta";     "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rw!("beta";     "(app (lam ?body) ?e)" => "(let ?e ?body)"),
        rw!("shift-const"; "(shift ?c)" => "?c" if is_const(var("?c"))),
        rw!("shift-apply"; "(shift (app ?a ?b))" => "(app (shift ?a) (shift ?b))"),
        rw!("shift-apply-rev"; "(app (shift ?a) (shift ?b))" => "(shift (app ?a ?b))"),
        rw!("let-app";  "(let ?e (app ?a ?b))" => "(app (let ?e ?a) (let ?e ?b))"),
        rw!("let-app-rev";  "(app (let ?e ?a) (let ?e ?b))" => "(let ?e (app ?a ?b))"),
        rw!("let-add";  "(let ?e (+   ?a ?b))" => "(+   (let ?e ?a) (let ?e ?b))"),
        rw!("let-add-rev";  "(+   (let ?e ?a) (let ?e ?b))" => "(let ?e (+   ?a ?b))"),
        rw!("let-eq";   "(let ?e (=   ?a ?b))" => "(=   (let ?e ?a) (let ?e ?b))"),
        rw!("let-eq-rev";   "(=   (let ?e ?a) (let ?e ?b))" => "(let ?e (=   ?a ?b))"),
        rw!("let-const";
            "(let ?e ?c)" => "?c" if is_const(var("?c"))),
        rw!("let-if";
            "(let ?e (if ?cond ?then ?else))" =>
            "(if (let ?e ?cond) (let ?e ?then) (let ?e ?else))"
        ),
        // rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
        rw!("let-var-same"; "(let ?e @0)" => "?e"),
        // rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
        //     if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-var-diff"; "(let ?e (shift ?body))" => "?body"),
        rw!("manufacture-let"; "(app (let ?v ?e) ?body)" => "(app (let ?v ?e) (let ?v (shift ?body)))"),
    ]
}

egg::test_fn! {
    db_simple_let, rules(),
    "(let 4 (+ 1 @0))"
    =>
    "5",
}

egg::test_fn! {
    db_simple_let2, rules(),
    "(let 4 (lam 1))"
    =>
    "1",
}

egg::test_fn! {
    db_single_lam, rules(),
    "(app (lam (+ 1 @0)) 2)" => "3",
}

egg::test_fn! {
    db_double_app, rules(),
    "(app (app (lam (lam (shift (@0)))) 1) 2)" => "1",
}

egg::test_fn! {
    db_compose_peano, rules(),
    "(let (lam (lam (lam (app (shift (shift @0)) (app (shift @0) @0)))))
     (let (lam (+ @0 1))
     (app (app (shift @0) @0) @0)))"
    =>
    "(lam (+ @0 2))"
}
