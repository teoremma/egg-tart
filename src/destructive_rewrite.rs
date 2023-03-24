use egg::*;
use fxhash::FxHashMap as HashMap;

// TODO the match_over function could just be a fold over the Ids, but this is
// easiest for me right now.
pub trait MatchOverLanguage {
    /// match_child takes as its first argument a child of self and its second
    /// argument the matching child of candidate.
    fn match_over<P>(&self, candidate: &Self, match_child: P) -> bool
    where Self: Sized, P: FnMut(&Id, &Id) -> bool;
}

// TODO: this and its applier can probably be generalized over languages L that
// implement match_enode
pub struct DestructiveRewrite<Language> {
    pub original_pattern: Pattern<Language>,
    pub add_pattern: Pattern<Language>,
}

impl<Language, Analysis> Applier<Language, Analysis> for DestructiveRewrite<Language>
where Language: egg::Language + MatchOverLanguage,
      Analysis: egg::Analysis<Language> {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Language, Analysis>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Language>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        // TODO: do we need a trait for the Analysis? It seems like the memo didn't do anything.
        // let memo = (rule_name, subst.clone(), self.original_pattern.ast.clone());
        // if egraph[eclass].data.previous_rewrites.contains(&memo) {
        //     return vec!();
        // }
        // egraph[eclass].data.previous_rewrites.insert(memo);
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
pub fn prune_enodes_matching<Language, Analysis>(egraph: &mut egg::EGraph<Language, Analysis>, rec_expr: &RecExpr<ENodeOrVar<Language>>, subst: &Subst, eclass: &Id, rule_name: Symbol) -> bool
where Language: MatchOverLanguage + egg::Language,
      Analysis: egg::Analysis<Language> {
    // let dr_enabled = match rule_name.as_str() {
    //     "if-true" => true,
    //     "if-false" => true,
    //     "if-elim" => true,
    //     "beta" => false,
    //     "let-app" => true,
    //     "let-add" => true,
    //     "let-eq" => true,
    //     "let-const" => true,
    //     "let-if" => false,
    //     "let-var-same" => true,
    //     "let-var-diff" => true,
    //     "let-lam-same" => false,
    //     "let-lam-diff" => false,
    //     _ => false,
    // };
    // if !dr_enabled {
    //     return false;
    // }
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
fn match_enode<Language, Analysis>(egraph: &egg::EGraph<Language, Analysis>, rec_expr: &RecExpr<ENodeOrVar<Language>>, rec_expr_id: &Id, subst: &Subst, enode: &Language, memo: &mut HashMap<(Id, Id), bool>) -> bool
where Language: MatchOverLanguage + egg::Language,
      Analysis: egg::Analysis<Language> {
    match &rec_expr[*rec_expr_id] {
        ENodeOrVar::ENode(n) => {
            enode.match_over(n, move |enode_id, re_id| {
                any_enode_in_eclass_matches(egraph, rec_expr, re_id, subst, enode_id, memo)
            })
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
fn any_enode_in_eclass_matches<Language, Analysis>(egraph: &egg::EGraph<Language, Analysis>, rec_expr: &RecExpr<ENodeOrVar<Language>>, rec_expr_id: &Id, subst: &Subst, eclass: &Id, memo: &mut HashMap<(Id, Id), bool>) -> bool
where Language: MatchOverLanguage + egg::Language,
      Analysis: egg::Analysis<Language> {
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
