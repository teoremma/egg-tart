use std::fmt::Display;
use std::str::FromStr;

use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;
use fxhash::FxHashMap as HashMap;

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
        "nop" = Nop([Id; 1]),

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

    fn increment_id(&self, increment: usize) -> Self {
        match self {
            DeBruijn::Add([id1, id2]) => DeBruijn::Add([increment_id(*id1, increment), increment_id(*id2, increment)]),
            DeBruijn::Eq([id1, id2]) => DeBruijn::Eq([increment_id(*id1, increment), increment_id(*id2, increment)]),
            DeBruijn::App([id1, id2]) => DeBruijn::App([increment_id(*id1, increment), increment_id(*id2, increment)]),
            DeBruijn::Lam([id]) => DeBruijn::Lam([increment_id(*id, increment)]),
            DeBruijn::Let([id1, id2]) =>
                DeBruijn::Let([increment_id(*id1, increment), increment_id(*id2, increment)]),
            DeBruijn::If([id1, id2, id3]) =>
                DeBruijn::If([increment_id(*id1, increment), increment_id(*id2, increment), increment_id(*id3, increment)]),
            DeBruijn::Shift([id]) => DeBruijn::Shift([increment_id(*id, increment)]),
            DeBruijn::Nop([id]) => DeBruijn::Nop([increment_id(*id, increment)]),
            DeBruijn::Bool(_) | DeBruijn::Num(_) | DeBruijn::Index(_) => self.to_owned()
        }
    }
}

fn increment_id(id: Id, increment: usize) -> Id {
    let id_as_usize: usize = id.into();
    (id_as_usize + increment).into()
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
        // rw!("fix";      "(fix ?v ?e)"             => "(let ?v (fix ?v ?e) ?e)"),
        // rw!("beta";     "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rw!("let";      "(let ?e ?body)" => "(app (lam ?body) ?e)"),
        rw!("beta";     "(app (lam ?body) ?e)" => {
            SketchGuidedBetaReduction {
                e: "?e".parse().unwrap(),
                body: "?body".parse().unwrap(),
            }
        }),
        // rw!("shift-const"; "(shift ?c)" => "?c" if is_const(var("?c"))),
        // rw!("shift-apply"; "(shift (app ?a ?b))" => "(app (shift ?a) (shift ?b))"),
        // rw!("let-app";  "(let ?e (app ?a ?b))" => "(app (let ?e ?a) (let ?e ?b))"),
        // rw!("let-add";  "(let ?e (+   ?a ?b))" => "(+   (let ?e ?a) (let ?e ?b))"),
        // rw!("let-eq";   "(let ?e (=   ?a ?b))" => "(=   (let ?e ?a) (let ?e ?b))"),
        // rw!("let-const";
        //     "(let ?e ?c)" => "?c" if is_const(var("?c"))),
        // rw!("let-if";
        //     "(let ?e (if ?cond ?then ?else))" =>
        //     "(if (let ?e ?cond) (let ?e ?then) (let ?e ?else))"
        // ),
        // // rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
        // rw!("let-var-same"; "(let ?e @0)" => "?e"),
        // // rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
        // //     if is_not_same_var(var("?v1"), var("?v2"))),
        // rw!("let-var-diff"; "(let ?e (shift ?body))" => "?body"),
        // rw!("abc"; "(app (let ?v ?e) ?body)" => "(app (let ?v ?e) (let ?v (shift ?body)))"),
        rw!("nop"; "(nop ?x)" => "?x"),
    ]
}

fn substitute_rec_expr(rec_expr: &mut RecExpr<DeBruijn>, seen: &mut HashSet<Id>, id: Id, subst_id: Id, target_index: u32) {
    if seen.contains(&id) {
        return;
    }
    seen.insert(id);
    match rec_expr[id] {
        DeBruijn::Index(DeBruijnIndex(idx)) => {
            // match
            if idx == target_index {
                rec_expr[id] = rec_expr[subst_id].to_owned();
            // unshift
            } else if idx > target_index {
                rec_expr[id] = DeBruijn::Index(DeBruijnIndex(idx - 1));
            }
        }
        DeBruijn::Shift([id]) => {
            // Substitutions cancel out shifts - we could avoid generating a new
            // term by pointing the parent to `id` but there's some edge-case
            // logic if `Shift` is the root. Let's do the stupid simple thing
            // for now.
            rec_expr[id] = DeBruijn::Nop([id]);
            if target_index != 0 {
                substitute_rec_expr(rec_expr, seen, id, subst_id, target_index - 1);
            }
        }
        DeBruijn::Lam([id]) => {
            substitute_rec_expr(rec_expr, seen, id, subst_id, target_index + 1);
        }
        DeBruijn::Let([id1, id2]) => {
            substitute_rec_expr(rec_expr, seen, id1, subst_id, target_index);
            substitute_rec_expr(rec_expr, seen, id2, subst_id, target_index + 1);
        }
        DeBruijn::Add([id1, id2]) | DeBruijn::Eq([id1, id2]) | DeBruijn::App([id1, id2]) => {
            substitute_rec_expr(rec_expr, seen, id1, subst_id, target_index);
            substitute_rec_expr(rec_expr, seen, id2, subst_id, target_index);
        }
        DeBruijn::Nop([id]) => {
            substitute_rec_expr(rec_expr, seen, id, subst_id, target_index);
        }
        DeBruijn::If([id1, id2, id3]) => {
            substitute_rec_expr(rec_expr, seen, id1, subst_id, target_index);
            substitute_rec_expr(rec_expr, seen, id2, subst_id, target_index);
            substitute_rec_expr(rec_expr, seen, id3, subst_id, target_index);
        }
        DeBruijn::Bool(_) | DeBruijn::Num(_) => {
            // Nothing to do
        }
    }
}

struct SketchGuidedBetaReduction {
    e: Var,
    body: Var
}

impl Applier<DeBruijn, DeBruijnAnalysis> for SketchGuidedBetaReduction {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<DeBruijn>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let e = subst[self.e];
        let body = subst[self.body];
        let extractor = Extractor::new(&egraph, AstSize);
        let (_, best_e) = extractor.find_best(e);
        let (_, best_body) = extractor.find_best(body);
        let e_rec_expr_len = best_e.as_ref().len();
        let e_id = e_rec_expr_len - 1;
        // Adjust the ids so we can put them at the end of the best_e rec expr.
        let adjusted_body_rec_expr: Vec<DeBruijn> = best_body
            .as_ref()
            .into_iter()
            .map(|expr| expr.increment_id(e_rec_expr_len))
            .collect();
        // Put both body and e into a single rec expr.
        let body_and_e_rec_expr: RecExpr<DeBruijn> = best_e
            .as_ref()
            .into_iter()
            .cloned()
            .chain(adjusted_body_rec_expr)
            .collect::<Vec<DeBruijn>>()
            .into();
        let body_id = body_and_e_rec_expr.as_ref().len() - 1;
        println!("prev_expr: {}", body_and_e_rec_expr);
        let mut new_rec_expr = body_and_e_rec_expr.clone();
        // println!("sym: {:?}, body: {}, e: {}", sym_to_replace, best_body, best_e);//, body_and_e_rec_expr.as_ref());
        substitute_rec_expr(&mut new_rec_expr, &mut HashSet::default(), body_id.into(), e_id.into(), 0);
        println!("new_expr: {}", new_rec_expr);
        // println!("end expr: {}", new_rec_expr);
        // for class in egraph.classes() {
        //     println!("id: {:?}, nodes: {:?}", class.id, class.nodes);
        // }
        // panic!();
        let new_id = egraph.add_expr(&new_rec_expr);
        egraph.union(eclass, new_id);
        vec!(new_id) // + changed_ids
    }
}

egg::test_fn! {
    db_simple_let, rules(),
    "(let 4 (+ 1 @0))"
    =>
    "5",
}

egg::test_fn! {
    db_simple_let2, rules(),
    "(let 4 (+ 1 @0))"
    =>
    "5",
}

egg::test_fn! {
    db_single_lam, rules(),
    "(app (lam (+ 1 @0)) 2)" => "3",
}

egg::test_fn! {
    db_double_app, rules(),
    "(app (app (lam (lam (@1))) 1) 2)" => "2",
}

egg::test_fn! {
    db_compose, rules(),
    "(let (lam (lam (lam (app @2 (app @1 @0)))))
     (let (lam (+ @0 1))
     (app (app @1 @0) @0)))"
    =>
    "(lam (+ @0 2))"
}

egg::test_fn! {
    db_compose_2, rules(),
    "(let (lam (lam (lam (app @2 (app @1 @0)))))
     (let (lam (+ @0 1))
     (app (app (app @1 @0) @0) 1)))"
    =>
    "3"
}
