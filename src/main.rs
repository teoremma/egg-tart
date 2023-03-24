mod debruijn;
mod lambda_baseline;
mod lambda;
// mod reps;
mod reps;
// use reps::named::Named;
// use reps::named::Named::*;
use reps::named::*;
mod lambda_destructive_rewrite;
mod phases;
mod benchmarks;
mod debruijn_small_step;

fn main() {
    let mut lhs = lam(lam(app(app(var(4), var(2)), lam(app(var(1), var(3))))));
    let mut rhs = lam(app(var(5), var(1)));
    lhs.apply(&rhs);
    println!("{:?}", lhs);
}
