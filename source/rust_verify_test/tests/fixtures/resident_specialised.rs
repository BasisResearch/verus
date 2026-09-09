use vstd::prelude::*;
verus! {
    mod a {
        use super::*;
        proof fn nonlinear_good(x: int, y: int) {
            assert((x + y) * (x + y) == x*x + 2*x*y + y*y) by(nonlinear_arith);
            assert(x*x >= 0) by(nonlinear_arith);
        }
        #[verifier::nonlinear]
        proof fn nonlinear_whole(x: int) { assert(x*x >= 0); }
        #[verifier::rlimit(3)]
        proof fn bits_good(x: u32) {
            assert(x & x == x) by(bit_vector);
            assert(x ^ x == 0) by(bit_vector);
        }
        proof fn bits_whole(x: u32) by(bit_vector)
            ensures x & x == x, x ^ x == 0,
        {}
    }
    mod b {
        use super::*;
        proof fn nonlinear_bad(x: int) {
            assert(x*x == x) by(nonlinear_arith);
        }
        proof fn bits_bad(x: u32) {
            assert(x & 0xff == x) by(bit_vector);
        }
        proof fn bits_quantified() {
            assert(forall|x: u32| #[trigger] (x ^ x) == 0) by(bit_vector);
        }
    }
}
