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