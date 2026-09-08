use reach_lib_bin::{double, Bump, Counter};

fn main() {
    let mut counter = Counter { n: double(21) };
    counter.bump();
    println!("{}", counter.n);
}
