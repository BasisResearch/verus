use reach_lib_bin::{double, Bump, Counter};

fn main() {
    let mut counter = Counter { n: double(21) };
    counter.bump();
    println!("{}", helper(counter.n));
}

/// Shares its name with a library function; the two must stay apart.
fn helper(n: u32) -> u32 {
    n
}
