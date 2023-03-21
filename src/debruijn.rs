use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;
use std::fmt::Display;
use std::str::FromStr;

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

        "fix" = Fix([Id; 2]),
        "app" = App([Id; 2]),
        "lam" = Lam([Id; 1]),
        "let" = Let([Id; 2]),
        "if" = If([Id; 3]),

        "shift" = Shift([Id; 1]),

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
            DeBruijn::Fix([id1, id2]) => {
                DeBruijn::Fix([increment_id(*id1, increment), increment_id(*id2, increment)])
            }
            DeBruijn::If([id1, id2, id3]) => DeBruijn::If([
                increment_id(*id1, increment),
                increment_id(*id2, increment),
                increment_id(*id3, increment),
            ]),
            DeBruijn::Shift([id]) => DeBruijn::Shift([increment_id(*id, increment)]),
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

fn is_dbi(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        println!("is_dbi({:?})", egraph[subst[v]]);
        true
    }
}

fn get_sym(eclass: Id, egraph: &EGraph) -> DeBruijnIndex {
    let nodes = &egraph[eclass].nodes;
    // This var should just point to a symbol
    match nodes[..] {
        [DeBruijn::Index(dbi)] => dbi,
        _ => panic!(
            "Nodes at id: {:?} are not just a single symbol, nodes: {:?},\negraph: {:?}",
            eclass, nodes, egraph
        ),
    }
}

fn substitute_rec_expr(
    rec_expr: &mut RecExpr<DeBruijn>,
    seen: &mut HashSet<Id>,
    id: Id,
    subst_sym: DeBruijnIndex,
    subst_id: Id,
) {
    if seen.contains(&id) {
        // println!("substitute_rec_expr: already seen {:?}", id);
        return;
    }
    // println!("substitute_rec_expr: visiting {:?} which is {:?}", id, rec_expr[id]);
    seen.insert(id);
    // println!(
    //     "substitute_rec_expr: {:?}, {:?}, {:?}, {:?}",
    //     rec_expr, subst_sym, id, subst_id
    // );
    match rec_expr[id] {
        DeBruijn::Add([id1, id2])
        | DeBruijn::Eq([id1, id2])
        | DeBruijn::App([id1, id2])
        | DeBruijn::Fix([id1, id2]) => {
            substitute_rec_expr(rec_expr, seen, id1, subst_sym, subst_id);
            substitute_rec_expr(rec_expr, seen, id2, subst_sym, subst_id);
        }
        DeBruijn::If([id1, id2, id3]) => {
            substitute_rec_expr(rec_expr, seen, id1, subst_sym, subst_id);
            substitute_rec_expr(rec_expr, seen, id2, subst_sym, subst_id);
            substitute_rec_expr(rec_expr, seen, id3, subst_sym, subst_id);
        }
        DeBruijn::Lam([id2]) => {
            substitute_rec_expr(rec_expr, seen, id2, subst_sym.increment(), subst_id);
        }
        DeBruijn::Let([id2, id3]) => {
            substitute_rec_expr(rec_expr, seen, id2, subst_sym, subst_id);
            substitute_rec_expr(rec_expr, seen, id3, subst_sym.increment(), subst_id);
        }
        DeBruijn::Shift([id2]) => {
            if subst_sym.0 > 0 {
                substitute_rec_expr(rec_expr, seen, id2, subst_sym.decrement(), subst_id);
            }
        }
        DeBruijn::Index(dbi) => {
            // println!("substitute_rec_expr: found index {:?} at id {:?}", dbi, id);
            if dbi.0 == subst_sym.0 {
                rec_expr[id] = rec_expr[subst_id].to_owned();
            } else if dbi.0 > subst_sym.0 {
                rec_expr[id] = DeBruijn::Index(dbi.decrement());
            }
        }
        DeBruijn::Bool(_) | DeBruijn::Num(_) => {
            // Nothing to do for all other non-recursive cases
        }
    }
}

struct ExtractionBasedSubstitution {
    e: Var,
    body: Var,
}

impl Applier<DeBruijn, DeBruijnAnalysis> for ExtractionBasedSubstitution {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<DeBruijn>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // let v = subst[self.v];
        let sym_to_replace = DeBruijnIndex(0);
        let e = subst[self.e];
        let body = subst[self.body];

        let extractor = Extractor::new(&egraph, AstSize);

        // let best_e = egraph.id_to_expr(e);
        // let best_body = egraph.id_to_expr(body);
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
        let mut new_rec_expr = body_and_e_rec_expr.clone();
        println!(
            "sym: {:?}, body: {}, e: {}",
            sym_to_replace, best_body, best_e
        ); //, body_and_e_rec_expr.as_ref());
        substitute_rec_expr(
            &mut new_rec_expr,
            &mut HashSet::default(),
            body_id.into(),
            sym_to_replace,
            e_id.into(),
        );

        // new_rec_expr.add(DeBruijn::Lam([body_id.into()]));
        println!("new_rec_expr: {}", new_rec_expr);
        let new_id = egraph.add_expr(&new_rec_expr);
        egraph.union(eclass, new_id);
        vec![new_id] // + changed_ids
    }
}

fn rules() -> Vec<Rewrite<DeBruijn, DeBruijnAnalysis>> {
    vec![
        // open term rules
        rw!("if-true";  "(if true ?then ?else)" => "?then"),
        rw!("if-false"; "(if false ?then ?else)" => "?else"),
        rw!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
        rw!("beta";     "(app (lam ?body) ?e)" => "(let ?e ?body)"),
        rw!("let";     "(let ?e ?body)" => {
            ExtractionBasedSubstitution {
                e: var("?e"),
                body: var("?body"),
            }
        }),
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
    "(let 4 (lam @1))"
    =>
    "(lam 4)",
}

egg::test_fn! {
    db_simple_let3, rules(),
    "(let 4 (lam @0))"
    =>
    "(lam @0)",
}

egg::test_fn! {
    db_single_lam, rules(),
    "(app (lam (+ 1 @0)) 2)" => "3",
}

egg::test_fn! {
    db_double_app, rules(),
    "(app (app (lam (lam @1)) 1) 2)" => "1",
}

egg::test_fn! {
    db_compose, rules(),
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
    db_double_let_lambdas, rules(),
    "(let
        (lam (+ @0 1))
        (let 
            (lam (+ @0 2))
            (lam (app @2 (app @1 @0)))
        )
    )"
    =>
    "(lam (+ @0 3))",
    // "(lam (+ @0 2))"
}
