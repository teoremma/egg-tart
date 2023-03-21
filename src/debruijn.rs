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

#[derive(Debug, Clone)]
enum DeBruijnAST {
    Bool(bool),
    Num(i32),
    Add(Box<DeBruijnAST>, Box<DeBruijnAST>),
    Eq(Box<DeBruijnAST>, Box<DeBruijnAST>),
    Fix(Box<DeBruijnAST>, Box<DeBruijnAST>),
    App(Box<DeBruijnAST>, Box<DeBruijnAST>),
    Lam(Box<DeBruijnAST>),
    Let(Box<DeBruijnAST>, Box<DeBruijnAST>),
    If(Box<DeBruijnAST>, Box<DeBruijnAST>, Box<DeBruijnAST>),
    Shift(Box<DeBruijnAST>),
    Index(DeBruijnIndex),
}

impl DeBruijnAST {
    pub fn from_rec_expr(rec_expr: &RecExpr<DeBruijn>) -> Self {
        let id = rec_expr.as_ref().len() - 1;
        from_rec_expr_helper(rec_expr, id.into())
    }
    pub fn to_rec_expr(&self) -> RecExpr<DeBruijn> {
        let mut expr_vec = vec!();
        to_rec_expr_helper(&mut expr_vec, self);
        RecExpr::from(expr_vec)
    }

    pub fn increment_free_vars(&self) -> Self {
        increment_free_vars_helper(self, None)
    }
}

fn from_rec_expr_helper(
    rec_expr: &RecExpr<DeBruijn>,
    id: Id,
) -> DeBruijnAST {
    // We assume no infinite loops (perahps a poor assumption).
    match rec_expr[id] {
        DeBruijn::Add([id1, id2]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            let arg2 = from_rec_expr_helper(rec_expr, id2);
            DeBruijnAST::Add(Box::new(arg1), Box::new(arg2))
        }
        DeBruijn::Eq([id1, id2]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            let arg2 = from_rec_expr_helper(rec_expr, id2);
            DeBruijnAST::Eq(Box::new(arg1), Box::new(arg2))

        }
        DeBruijn::App([id1, id2]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            let arg2 = from_rec_expr_helper(rec_expr, id2);
            DeBruijnAST::App(Box::new(arg1), Box::new(arg2))

        }
        DeBruijn::Fix([id1, id2]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            let arg2 = from_rec_expr_helper(rec_expr, id2);
            DeBruijnAST::Fix(Box::new(arg1), Box::new(arg2))
        }
        DeBruijn::If([id1, id2, id3]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            let arg2 = from_rec_expr_helper(rec_expr, id2);
            let arg3 = from_rec_expr_helper(rec_expr, id3);
            DeBruijnAST::If(Box::new(arg1), Box::new(arg2), Box::new(arg3))
        }
        DeBruijn::Lam([id1]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            DeBruijnAST::Lam(Box::new(arg1))
        }
        DeBruijn::Let([id1, id2]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            let arg2 = from_rec_expr_helper(rec_expr, id2);
            DeBruijnAST::Let(Box::new(arg1), Box::new(arg2))
        }
        DeBruijn::Shift([id1]) => {
            let arg1 = from_rec_expr_helper(rec_expr, id1);
            DeBruijnAST::Shift(Box::new(arg1))
        }
        DeBruijn::Index(dbi) => {
            DeBruijnAST::Index(dbi)
        }
        DeBruijn::Bool(b) => {
            DeBruijnAST::Bool(b)
        }
        DeBruijn::Num(n) => {
            DeBruijnAST::Num(n)
        }
    }
}

fn to_rec_expr_helper(expr_vec: &mut Vec<DeBruijn>, expr: &DeBruijnAST) -> Id {
    let db_expr = match expr {
        DeBruijnAST::Add(arg1, arg2) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            let id2 = to_rec_expr_helper(expr_vec, arg2);
            DeBruijn::Add([id1, id2])
        }
        DeBruijnAST::Eq(arg1, arg2) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            let id2 = to_rec_expr_helper(expr_vec, arg2);
            DeBruijn::Eq([id1, id2])

        }
        DeBruijnAST::App(arg1, arg2) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            let id2 = to_rec_expr_helper(expr_vec, arg2);
            DeBruijn::App([id1, id2])

        }
        DeBruijnAST::Fix(arg1, arg2) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            let id2 = to_rec_expr_helper(expr_vec, arg2);
            DeBruijn::Fix([id1, id2])
        }
        DeBruijnAST::If(arg1, arg2, arg3) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            let id2 = to_rec_expr_helper(expr_vec, arg2);
            let id3 = to_rec_expr_helper(expr_vec, arg3);
            DeBruijn::If([id1, id2, id3])
        }
        DeBruijnAST::Lam(arg1) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            DeBruijn::Lam([id1])
        }
        DeBruijnAST::Let(arg1, arg2) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            let id2 = to_rec_expr_helper(expr_vec, arg2);
            DeBruijn::Let([id1, id2])
        }
        DeBruijnAST::Shift(arg1) => {
            let id1 = to_rec_expr_helper(expr_vec, arg1);
            DeBruijn::Shift([id1])
        }
        DeBruijnAST::Index(dbi) => {
            DeBruijn::Index(*dbi)
        }
        DeBruijnAST::Bool(b) => {
            DeBruijn::Bool(*b)
        }
        DeBruijnAST::Num(n) => {
            DeBruijn::Num(*n)
        }
    };
    expr_vec.push(db_expr);
    (expr_vec.len() - 1).into()
}

fn increment_free_vars_helper(expr: &DeBruijnAST, bound_level: Option<u32>) -> DeBruijnAST {
    match expr {
        DeBruijnAST::Add(arg1, arg2) => {
            let new_arg1 = increment_free_vars_helper(arg1, bound_level);
            let new_arg2 = increment_free_vars_helper(arg2, bound_level);
            DeBruijnAST::Add(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::Eq(arg1, arg2) => {
            let new_arg1 = increment_free_vars_helper(arg1, bound_level);
            let new_arg2 = increment_free_vars_helper(arg2, bound_level);
            DeBruijnAST::Eq(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::App(arg1, arg2) => {
            let new_arg1 = increment_free_vars_helper(arg1, bound_level);
            let new_arg2 = increment_free_vars_helper(arg2, bound_level);
            DeBruijnAST::App(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::Fix(arg1, arg2) => {
            let new_arg1 = increment_free_vars_helper(arg1, bound_level);
            let new_arg2 = increment_free_vars_helper(arg2, bound_level.map(|lvl| lvl + 1));
            DeBruijnAST::Fix(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::If(arg1, arg2, arg3) => {
            let new_arg1 = increment_free_vars_helper(arg1, bound_level);
            let new_arg2 = increment_free_vars_helper(arg2, bound_level);
            let new_arg3 = increment_free_vars_helper(arg3, bound_level);
            DeBruijnAST::If(Box::new(new_arg1), Box::new(new_arg2), Box::new(new_arg3))
        }
        DeBruijnAST::Lam(arg1) => {
            let new_arg1 = increment_free_vars_helper(arg1, bound_level.map(|lvl| lvl + 1));
            DeBruijnAST::Lam(Box::new(new_arg1))
        }
        DeBruijnAST::Let(arg1, arg2) => {
            let new_arg1 = increment_free_vars_helper(arg1, bound_level);
            let new_arg2 = increment_free_vars_helper(arg2, bound_level.map(|lvl| lvl + 1));
            DeBruijnAST::Let(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::Shift(arg2) => {
            if let Some(lvl) = bound_level {
                if lvl > 0 {
                    increment_free_vars_helper(arg2, bound_level.map(|lvl| lvl - 1))
                } else {
                    expr.clone()
                }
            } else {
                expr.clone()
            }
        }
        DeBruijnAST::Index(dbi) => {
            // unbound
            if Some(dbi.0) > bound_level {
                DeBruijnAST::Index(dbi.increment())
            // bound
            } else {
                DeBruijnAST::Index(*dbi)
            }
        }
        DeBruijnAST::Bool(b) => {
            DeBruijnAST::Bool(*b)
        }
        DeBruijnAST::Num(n) => {
            DeBruijnAST::Num(*n)
        }
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
        merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn make(egraph: &EGraph, enode: &DeBruijn) -> Data {
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

fn substitute(
    body: &DeBruijnAST,
    id: DeBruijnIndex,
    subst: &DeBruijnAST,
) -> DeBruijnAST {
    match body {
        DeBruijnAST::Add(arg1, arg2) => {
            let new_arg1 = substitute(arg1, id, subst);
            let new_arg2 = substitute(arg2, id, subst);
            DeBruijnAST::Add(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::Eq(arg1, arg2) => {
            let new_arg1 = substitute(arg1, id, subst);
            let new_arg2 = substitute(arg2, id, subst);
            DeBruijnAST::Eq(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::App(arg1, arg2) => {
            let new_arg1 = substitute(arg1, id, subst);
            let new_arg2 = substitute(arg2, id, subst);
            DeBruijnAST::App(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::Fix(arg1, arg2) => {
            let new_arg1 = substitute(arg1, id, subst);
            let new_arg2 = substitute(arg2, id.increment(), &subst.increment_free_vars());
            DeBruijnAST::Fix(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::If(arg1, arg2, arg3) => {
            let new_arg1 = substitute(arg1, id, subst);
            let new_arg2 = substitute(arg2, id, subst);
            let new_arg3 = substitute(arg3, id, subst);
            DeBruijnAST::If(Box::new(new_arg1), Box::new(new_arg2), Box::new(new_arg3))
        }
        DeBruijnAST::Lam(arg1) => {
            let new_arg1 = substitute(arg1, id.increment(), &subst.increment_free_vars());
            DeBruijnAST::Lam(Box::new(new_arg1))
        }
        DeBruijnAST::Let(arg1, arg2) => {
            let new_arg1 = substitute(arg1, id, subst);
            let new_arg2 = substitute(arg2, id.increment(), &subst.increment_free_vars());
            DeBruijnAST::Let(Box::new(new_arg1), Box::new(new_arg2))
        }
        DeBruijnAST::Shift(arg2) => {
            if id.0 > 0 {
                substitute(arg2, id.decrement(), subst)
            } else {
                body.to_owned()
            }
        }
        DeBruijnAST::Index(dbi) => {
            // println!("substitute_rec_expr: found index {:?} at arg {:?}", dbi, arg);
            if dbi.0 == id.0 {
                subst.clone()
            } else if dbi.0 > id.0 {
                DeBruijnAST::Index(dbi.decrement())
            } else {
                body.to_owned()
            }
        }
        DeBruijnAST::Bool(_) | DeBruijnAST::Num(_) => {
            body.to_owned()
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

        let best_e = DeBruijnAST::from_rec_expr(&extractor.find_best(e).1);
        let best_body = DeBruijnAST::from_rec_expr(&extractor.find_best(body).1);

        println!("e: {}, body: {}", best_e.to_rec_expr(), best_body.to_rec_expr());
        let substituted_body = substitute(&best_body, DeBruijnIndex(0), &best_e);
        println!("subst_body: {}", substituted_body.to_rec_expr());

        // // Adjust the ids so we can put them at the end of the best_e rec expr.
        // let adjusted_body_rec_expr: Vec<DeBruijn> = best_body
        //     .as_ref()
        //     .into_iter()
        //     .map(|expr| expr.increment_id(e_rec_expr_len))
        //     .collect();
        // // Put both body and e into a single rec expr.
        // let body_and_e_rec_expr: RecExpr<DeBruijn> = best_e
        //     .as_ref()
        //     .into_iter()
        //     .cloned()
        //     .chain(adjusted_body_rec_expr)
        //     .collect::<Vec<DeBruijn>>()
        //     .into();
        // let body_id = body_and_e_rec_expr.as_ref().len() - 1;
        // let mut new_rec_expr = body_and_e_rec_expr.clone();
        // println!(
        //     "sym: {:?}, body: {}, e: {}",
        //     sym_to_replace, best_body, best_e
        // ); //, body_and_e_rec_expr.as_ref());
        // substitute_rec_expr(
        //     &mut new_rec_expr,
        //     &mut HashSet::default(),
        //     body_id.into(),
        //     sym_to_replace,
        //     e_id.into(),
        // );

        // println!("new_rec_expr: {}", new_rec_expr);
        // let new_id = egraph.add_expr(&new_rec_expr);
        let new_id = egraph.add_expr(&substituted_body.to_rec_expr());
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
        // subst rules
        // rw!("fix";      "(fix ?v ?e)"             => "(let (fix ?v ?e) ?e)"),
        // rw!("beta";     "(app (lam ?body) ?e)" => "(let ?e ?body)"),
        // // rw!("shift";    "(shift ?e)"             => "(shift ?e)" if is_dbi(var("?e"))),
        // rw!("shift-const"; "(shift ?c)" => "?c" if is_const(var("?c"))),
        // rw!("shift-apply"; "(shift (app ?a ?b))" => "(app (shift ?a) (shift ?b))"),
        // rw!("shift-apply-rev"; "(app (shift ?a) (shift ?b))" => "(shift (app ?a ?b))"),
        // rw!("let-app";  "(let ?e (app ?a ?b))" => "(app (let ?e ?a) (let ?e ?b))"),
        // rw!("let-app-rev";  "(app (let ?e ?a) (let ?e ?b))" => "(let ?e (app ?a ?b))"),
        // rw!("let-add";  "(let ?e (+   ?a ?b))" => "(+   (let ?e ?a) (let ?e ?b))"),
        // rw!("let-add-rev";  "(+   (let ?e ?a) (let ?e ?b))" => "(let ?e (+   ?a ?b))"),
        // rw!("let-eq";   "(let ?e (=   ?a ?b))" => "(=   (let ?e ?a) (let ?e ?b))"),
        // rw!("let-eq-rev";   "(=   (let ?e ?a) (let ?e ?b))" => "(let ?e (=   ?a ?b))"),
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
        // rw!("manufacture-let"; "(app (let ?v ?e) ?body)" => "(app (let ?v ?e) (let ?v (shift ?body)))"),
        // rw!("let-lam"; "(let ?e (lam ?body))" => {
        //     ExtractionBasedSubstitution {
        //         e: var("?e"),
        //         body: var("?body"),
        //     }
        // }),
        rw!("beta";     "(app (lam ?body) ?e)" => {
            ExtractionBasedSubstitution {
                e: var("?e"),
                body: var("?body"),
            }
        }),
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
}
