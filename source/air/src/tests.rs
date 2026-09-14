use crate::ast::CommandX;
use crate::context::{SmtSolver, ValidityResult};
use crate::messages::Reporter;
#[allow(unused_imports)]
use crate::parser::Parser;
#[allow(unused_imports)]
use crate::printer::{macro_push_node, str_to_node};
#[allow(unused_imports)]
use sise::TreeNode as Node;

#[allow(dead_code)]
fn run_nodes_as_test(should_typecheck: bool, should_be_valid: bool, nodes: &[sise::TreeNode]) {
    let message_interface = std::sync::Arc::new(crate::messages::AirMessageInterface {});
    let reporter = Reporter {};
    // TODO: Support testing with cvc5 too
    let mut air_context = crate::context::Context::new(message_interface.clone(), SmtSolver::Z3);
    air_context.set_z3_param("air_recommended_options", "true");
    match Parser::new(message_interface.clone()).nodes_to_commands(&nodes) {
        Ok(commands) => {
            for command in commands.iter() {
                let result = air_context.command(
                    &*message_interface,
                    &reporter,
                    &command,
                    Default::default(),
                );
                // A query that fails to type-check opens no query to finish.
                let opened_query = !matches!(result, ValidityResult::TypeError(_));
                match (&**command, should_typecheck, should_be_valid, result) {
                    (_, false, _, ValidityResult::TypeError(_)) => {}
                    (_, true, _, ValidityResult::TypeError(s)) => {
                        panic!("type error: {}", s);
                    }
                    (_, _, true, ValidityResult::Valid(..)) => {} // REVIEW: test unsat_core output
                    (_, _, false, ValidityResult::Invalid(..)) => {}
                    (CommandX::CheckValid(_), _, _, res) => {
                        panic!("unexpected result {:?}", res);
                    }
                    _ => {}
                }
                if opened_query && matches!(**command, CommandX::CheckValid(..)) {
                    air_context.finish_query();
                }
            }
        }
        Err(s) => {
            println!("{}", s);
            panic!();
        }
    }
}

#[allow(unused_macros)]
macro_rules! yes {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(true, true, &v)
       }
    };
}

#[allow(unused_macros)]
macro_rules! no {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(true, false, &v)
       }
    };
}

#[allow(unused_macros)]
macro_rules! untyped {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(false, false, &v)
       }
    };
}

#[test]
fn yes_true() {
    yes!(
        (check-valid
            (assert true)
        )
    );
}

#[test]
fn no_false() {
    no!(
        (check-valid
            (assert false)
        )
    );
}

#[test]
fn yes_int_const() {
    yes!(
        (check-valid
            (assert
                (= (+ 2 2) 4)
            )
        )
    );
}

#[test]
fn no_int_const() {
    no!(
        (check-valid
            (assert
                (= (+ 2 2) 5)
            )
        )
    );
}

#[test]
fn yes_int_vars() {
    yes!(
        (check-valid
            (declare-const x Int)
            (declare-const y Int)
            (declare-const z Int)
            (assert
                (= (+ x y z) (+ z y x))
            )
        )
    );
}

#[test]
fn no_int_vars() {
    no!(
        (check-valid
            (declare-const x Int)
            (declare-const y Int)
            (assert
                (= (+ x y) (+ y y))
            )
        )
    );
}

#[test]
fn yes_int_neg() {
    yes!(
        (check-valid
            (declare-const x Int)
            (assert
                (= (+ x (- 2)) (- x 2))
            )
        )
    );
}

#[test]
fn yes_int_axiom() {
    yes!(
        (check-valid
            (declare-const x Int)
            (axiom (> x 3))
            (assert
                (>= x 3)
            )
        )
    );
}

#[test]
fn no_int_axiom() {
    no!(
        (check-valid
            (declare-const x Int)
            (axiom (>= x 3))
            (assert
                (> x 3)
            )
        )
    );
}

#[test]
fn yes_float() {
    yes!(
        (check-valid
            (declare-const x (_ FloatingPoint 2 3))
            (declare-const y (_ FloatingPoint 2 3))
            (assert
                (= ({str_to_node("fp.add")} RNE x y) ({str_to_node("fp.add")} RNE y x))
            )
        )
    );
}

#[test]
fn no_float() {
    no!(
        (check-valid
            (declare-const x (_ FloatingPoint 2 3))
            (declare-const y (_ FloatingPoint 2 3))
            (assert
                (= ({str_to_node("fp.add")} RNE x y) (fp (_ bv0 1) (_ bv2 2) (_ bv2 2)))
            )
        )
    );
}

#[test]
fn yes_test_block() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (assert (>= x 3))
                (assume (> x 5))
                (assert (>= x 5))
            )
        )
    );
}

#[test]
fn no_test_block() {
    no!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (assert (>= x 3))
                (assert (>= x 5))
                (assume (> x 5))
            )
        )
    );
}

#[test]
fn yes_test_block_nest() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (block
                    (assert (>= x 3))
                    (assume (> x 5))
                )
                (assert (>= x 5))
            )
        )
    );
}

#[test]
fn yes_global() {
    yes!(
        (push)
            (axiom false)
            (check-valid
                (assert false)
            )
        (pop)
    );
}

#[test]
fn no_global() {
    no!(
        (push)
            (axiom false)
        (pop)
        (check-valid
            (assert false)
        )
    );
}

#[test]
fn yes_type() {
    yes!(
        (check-valid
            (declare-sort T 0)
            (declare-const x T)
            (assert
                (= x x)
            )
        )
    );
}

#[test]
fn no_type() {
    no!(
        (check-valid
            (declare-sort T 0)
            (declare-const x T)
            (declare-const y T)
            (assert
                (= x y)
            )
        )
    );
}

#[test]
fn yes_assign() {
    yes!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (assign x (+ x 1))
                (assert (= x 102))
                (assert (= y 200))
            )
        )
    );
}

#[test]
fn no_assign() {
    no!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (assign x (+ x 1))
                (assert (not (= x 102)))
            )
        )
    );
}

#[test]
fn yes_havoc() {
    yes!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (havoc x)
                (assert (= y 200))
            )
        )
    );
}

#[test]
fn no_havoc() {
    no!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (havoc y)
                (assert (= y 200))
            )
        )
    );
}

#[test]
fn yes_snapshot() {
    yes!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (snapshot A)
                (snapshot B)
                (assign x (+ x 1))
                (assert (= (old A x) 101))
                (assert (= (old B x) 101))
                (assert (= x 102))
                (assert (= y 200))
                (snapshot A)
                (assert (= (old A x) 102))
                (assert (= (old B x) 101))
            )
        )
    )
}

#[test]
fn yes_test_switch1() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (switch
                    (assume (> x 20))
                    (assume (< x 10))
                )
                (assert (or (> x 20) (< x 10)))
            )
        )
    );
}

#[test]
fn no_test_switch1() {
    no!(
        (check-valid
            (declare-const x Int)
            (block
                (switch
                    (assume (> x 20))
                    (assume (< x 10))
                )
                (assert (> x 20))
            )
        )
    );
}

#[test]
fn yes_test_switch2() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (assign x 10)
                (switch
                    (block
                    )
                    (assign x 15)
                    (block
                        (assign x 20)
                        (assign x (+ x 30))
                        (assign x (- x 40))
                    )
                    (assign x (+ x 7))
                )
                (assert (>= x 10))
                (assert (<= x 20))
            )
        )
    );
}

#[test]
fn no_test_switch2() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (assign x 10)
                (switch
                    (block
                    )
                    (assign x 15)
                    (block
                        (assign x 20)
                        (assign x (+ x 30))
                        (assign x (- x 40))
                    )
                    (assign x (+ x 7))
                )
                (assert (> x 10))
                (assert (<= x 20))
            )
        )
    );
}

#[test]
fn no_test_switch3() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (assign x 10)
                (switch
                    (block
                    )
                    (assign x 15)
                    (block
                        (assign x 20)
                        (assign x (+ x 30))
                        (assign x (- x 40))
                    )
                    (assign x (+ x 7))
                )
                (assert (>= x 10))
                (assert (< x 17))
            )
        )
    );
}

#[test]
fn untyped_scope1() {
    untyped!(
        (declare-const x Int)
        (declare-const x Int) // error: x already in scope
    );
}

#[test]
fn untyped_scope2() {
    untyped!(
        (declare-const x Int)
        (push)
            (declare-const x Int) // error: x already in scope
        (pop)
    );
}

#[test]
fn untyped_scope3() {
    untyped!(
        (declare-const x Int)
        (check-valid
            (declare-const x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope4() {
    untyped!(
        (declare-const x Int)
        (check-valid
            (declare-var x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope5() {
    untyped!(
        (declare-const "x@0" Int)
        (check-valid
            (declare-var x Int) // error: x@0 already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope6() {
    untyped!(
        (declare-var x Int) // error: declare-var not allowed in global scope
    );
}

#[test]
fn untyped_scope7() {
    untyped!(
        (declare-const x Int)
        (declare-fun x (Int Int) Int) // error: x already in scope
    );
}

#[test]
fn yes_scope1() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (push)
            (declare-const x Int)
        (pop)
    );
}

#[test]
fn yes_scope2() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (declare-const x Int)
    );
}

#[test]
fn yes_scope3() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (check-valid
            (declare-var x Int)
            (assert true)
        )
    );
}

#[test]
fn yes_fun1() {
    yes!(
        (check-valid
            (declare-fun f (Int Bool) Bool)
            (block
                (assume (f 10 true))
                (assert (f 10 true))
            )
        )
    )
}

#[test]
fn no_fun1() {
    no!(
        (check-valid
            (declare-fun f (Int Bool) Bool)
            (block
                (assume (f 10 true))
                (assert (f 11 true))
            )
        )
    )
}

#[test]
fn no_typing1() {
    untyped!(
        (axiom 10)
    )
}

#[test]
fn no_typing2() {
    untyped!(
        (axiom b)
    )
}

#[test]
fn no_typing3() {
    untyped!(
        (declare-fun f (Int Bool) Bool)
        (axiom (f 10))
    )
}

#[test]
fn no_typing4() {
    untyped!(
        (declare-fun f (Int Bool) Bool)
        (axiom (f 10 20))
    )
}

#[test]
fn no_typing5() {
    untyped!(
        (check-valid
            (declare-var x Int)
            (assign x true)
        )
    )
}

#[test]
fn yes_let1() {
    yes!(
        (check-valid
            (assert (let ((x 10) (y 20)) (< x y)))
        )
    )
}

#[test]
fn yes_let2() {
    yes!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        40
                        (let ((x (+ x 10))) (+ x y)) // can shadow other let/forall bindings
                    )
                )
            )
        )
    )
}

#[test]
fn yes_let3() {
    yes!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        (let ((x (+ x 10))) (+ x y)) // can shadow other let/forall bindings
                        (+ x x y) // make sure old values are restored here
                    )
                )
            )
        )
    )
}

#[test]
fn yes_let4() {
    yes!(
        (check-valid
            (assert
                (let ((x true) (y 20))
                    (and
                        (=
                            (let ((x (+ y 10))) (+ x y))
                            50
                        )
                        x // make sure old type is restored here
                    )
                )
            )
        )
    )
}

#[test]
fn untyped_let1() {
    untyped!(
        (check-valid
            (assert (let ((x 10) (x 20)) true)) // no duplicates allowed in single let
        )
    )
}

#[test]
fn untyped_let2() {
    untyped!(
        (declare-const y Int)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn untyped_let3() {
    untyped!(
        (declare-fun y (Int) Int)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn untyped_let4() {
    untyped!(
        (declare-sort y 0)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn no_let1() {
    no!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        (let ((x (+ x 10))) (+ x y))
                        (+ x y) // make sure old values are restored here
                    )
                )
            )
        )
    )
}

#[test]
fn yes_forall1() {
    yes!(
        (check-valid
            (assert
                (forall ((i Int)) true)
            )
        )
    )
}

#[test]
fn yes_forall2() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall3() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall4() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (declare-fun g (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((g i j))
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall5() {
    yes!(
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Bool)
        (axiom
            (forall ((i Int) (j Int)) (!
                (=> (f i) (g j))
                :pattern ((f i) (g j))
            ))
        )
        (check-valid
            (assert
                (=> (f 10) (g 10))
            )
        )
    )
}

#[test]
fn no_forall1() {
    no!(
        (check-valid
            (assert
                (forall ((i Int)) false)
            )
        )
    )
}

#[test]
fn no_forall2() {
    no!(
        (declare-fun f (Int Int) Bool)
        (declare-fun g (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((g i j))
                    ))
                    (f 10 20) // doesn't match (g i j)
                )
            )
        )
    )
}

#[test]
fn untyped_forall1() {
    untyped!(
        (check-valid
            (assert
                (let
                    ((
                        x
                        (forall ((i Int)) i)
                    ))
                    true
                )
            )
        )
    )
}

#[test]
fn yes_exists1() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (f 10 20)
                    (exists ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                )
            )
        )
    )
}

#[test]
fn no_exists1() {
    no!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (exists ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_ite1() {
    yes!(
        (check-valid
            (block
                (assert (= (ite true 10 20) 10))
                (assert (= (ite false 10 20) 20))
            )
        )
    )
}

#[test]
fn no_ite1() {
    no!(
        (check-valid
            (assert (= (ite true 10 20) 20))
        )
    )
}

#[test]
fn untyped_ite1() {
    untyped!(
        (check-valid
            (assert (= (ite 0 10 20) 20))
        )
    )
}

#[test]
fn untyped_ite2() {
    untyped!(
        (check-valid
            (assert (= (ite true 10 true) 20))
        )
    )
}

#[test]
fn yes_distinct() {
    yes!(
        (check-valid
            (assert (distinct 10 20 30))
        )
    )
}

#[test]
fn no_distinct() {
    no!(
        (check-valid
            (assert (distinct 10 20 10))
        )
    )
}

#[test]
fn untyped_distinct() {
    untyped!(
        (check-valid
            (assert (distinct 10 20 true))
        )
    )
}

#[test]
fn yes_datatype1() {
    yes!(
        (declare-datatypes ((IntPair 0)) (
            (
                (int_pair
                    (ip1 Int)
                    (ip2 Int)
                )
            )
        ))
        (check-valid
            (declare-const x IntPair)
            (block
                (assume (= x (int_pair 10 20)))
                (assert (= 10 (ip1 x)))
            )
        )
    )
}

#[test]
fn yes_datatype2() {
    yes!(
        (declare-datatypes ((Tree 0) (Pair 0)) (
            (
                (empty)
                (full
                    (children Pair)
                )
            )
            (
                (pair
                    (fst Tree)
                    (snd Tree)
                )
            )
        ))
        (check-valid
            (declare-const x Tree)
            (block
                (assume (= x (full (pair (empty) (empty)))))
                (assert (= (empty) (fst (children x))))
                (assert (is-empty (snd (children x))))
            )
        )
    )
}

#[test]
fn yes_deadend() {
    yes!(
        (declare-const b Bool)
        (check-valid
            (block
                (assume b)
                (deadend
                    (block
                        (assert b)
                    )
                )
                (assert b)
            )
        )
    )
}

#[test]
fn no_deadend1() {
    no!(
        (declare-const b Bool)
        (check-valid
            (block
                (deadend
                    (block
                        (assume b)
                        (assert b)
                    )
                )
                (assert b)
            )
        )
    )
}

#[test]
fn no_deadend2() {
    no!(
        (declare-const b Bool)
        (check-valid
            (block
                (deadend
                    (block
                        (assume b)
                        (assert false)
                    )
                )
                (assert b)
            )
        )
    )
}

#[test]
fn typed_break1() {
    yes!(
        (check-valid
            (breakable L (break L))
        )
    )
}

#[test]
fn typed_break2() {
    yes!(
        (check-valid
            (breakable L (break L))
        )
        (check-valid
            (breakable L (break L))
        )
    )
}

#[test]
fn untyped_break1() {
    untyped!(
        (check-valid
            (breakable L (assert false))
        )
        (check-valid
            (break L)
        )
    )
}

#[test]
fn untyped_break2() {
    untyped!(
        (check-valid
            (breakable L1 (break L2))
        )
    )
}

#[test]
fn untyped_break3() {
    untyped!(
        (check-valid
            (block
                (break L)
                (breakable L (block))
            )
        )
    )
}

#[test]
fn untyped_break4() {
    untyped!(
        (check-valid
            (block
                (breakable L (block))
                (break L)
            )
        )
    )
}

#[test]
fn untyped_break5() {
    untyped!(
        (check-valid
            (switch
                (breakable L (block))
                (break L)
            )
        )
    )
}

#[test]
fn untyped_break6() {
    untyped!(
        (check-valid
            (switch
                (breakable L (block))
                (breakable L (block))
            )
        )
    )
}

#[test]
fn yes_break1() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (block
                        (assign x 9)
                        (assign x 10)
                    )
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break1() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 9)
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break1b() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn yes_break2() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 19)
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break2() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 19)
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break2b() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 19)
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20)))
            )
        )
    )
}

#[test]
fn yes_break3() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L1 (switch
                    (block
                        (assign x 20)
                        (break L1)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (breakable L2 (switch
                            (assign x 40)
                            (block
                                (assign x (+ x 1))
                                (break L2)
                            )
                            (block
                                (assign x (+ x 2))
                                (break L1)
                            )
                        ))
                        (assign x (+ x 5))
                        (break L1)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 32) (= x 36) (= x 45)))
            )
        )
    )
}

#[test]
fn no_break3() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L1 (switch
                    (block
                        (assign x 20)
                        (break L1)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (breakable L2 (switch
                            (assign x 40)
                            (block
                                (assign x (+ x 1))
                                (break L1)
                            )
                            (block
                                (assign x (+ x 2))
                                (break L2)
                            )
                        ))
                        (assign x (+ x 5))
                        (break L1)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 32) (= x 36) (= x 45)))
            )
        )
    )
}

#[test]
fn yes_array1() {
    yes!(
        (check-valid
            (assert (=
                20
                (apply Int
                    (array 10 20 30)
                    1
                )
            ))
        )
    )
}

#[test]
fn untyped_array1() {
    untyped!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (array 10 true 30)
                    1
                )
            ))
        )
    )
}

#[test]
fn no_array1() {
    no!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (array 10 20 30)
                    2
                )
            ))
        )
    )
}

#[test]
fn yes_array2() {
    yes!(
        (check-valid
            (assert (=
                6
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (array 10 20 (+ x y 1))
                        )
                        2
                        3
                    )
                    2
                )
            ))
        )
    )
}

#[test]
fn no_array2() {
    no!(
        (check-valid
            (assert (=
                5
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (array 10 20 (+ x y 1))
                        )
                        2
                        3
                    )
                    2
                )
            ))
        )
    )
}

#[test]
fn yes_array3() {
    yes!(
        (check-valid
            (assert
                (=
                    (array (+ (- 10 (+ 2 2)) 5))
                    (array (+ (- 10 4) 5))
                )
            )
        )
    )
}

#[test]
fn no_array3() {
    no!(
        (check-valid
            (assert
                (=
                    (array (+ (- 10 (+ 2 3)) 5))
                    (array (+ (- 10 4) 5))
                )
            )
        )
    )
}

#[test]
fn yes_empty_array() {
    yes!(
        (check-valid
            (assert (= (array) (array)))
        )
    )
}

#[test]
fn yes_lambda1() {
    yes!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (lambda ((x Int) (y Int)) (+ x y 5))
                    2
                    3
                )
            ))
        )
    )
}

#[test]
fn untyped_lambda1() {
    untyped!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (lambda ((x Int) (y Int)) (+ x y 5))
                    3
                )
            ))
        )
    )
}

#[test]
fn no_lambda1() {
    no!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (lambda ((x Int) (y Int)) (+ x y 4))
                    2
                    3
                )
            ))
        )
    )
}

#[test]
fn yes_lambda2() {
    yes!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (lambda ((z Int)) (+ x y z 1))
                        )
                        2
                        3
                    )
                    4
                )
            ))
        )
    )
}

#[test]
fn no_lambda2() {
    no!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (lambda ((z Int)) (+ x y z 1))
                        )
                        2
                        3
                    )
                    5
                )
            ))
        )
    )
}

#[test]
fn yes_lambda3() {
    yes!(
        (check-valid
            (assert
                (let ((g
                        (let (
                                (f (lambda ((x Int)) (+ x 1)))
                            )
                            f
                        )
                    ))
                    (=
                        (apply Int g 3)
                        4
                    )
                )
            )
        )
    )
}

#[test]
fn no_lambda3() {
    no!(
        (check-valid
            (assert
                (let ((g
                        (let (
                                (f (lambda ((x Int)) (+ x 1)))
                            )
                            f
                        )
                    ))
                    (=
                        (apply Int g 3)
                        5
                    )
                )
            )
        )
    )
}

#[test]
fn yes_lambda4() {
    yes!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 4) yy))
                )
            )
        )
    )
}

#[test]
fn no_lambda4a() {
    no!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((y Int) (x Int)) (+ (- x 4) y))
                )
            )
        )
    )
}

#[test]
fn no_lambda4b() {
    no!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x 5) y))
                    (lambda ((x Int) (y Int)) (+ (- x 4) y))
                )
            )
        )
    )
}

#[test]
fn yes_lambda5() {
    yes!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 4) yy))
                )
            )
        )
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 4) yy))
                )
            )
        )
    )
}

#[test]
fn no_lambda5() {
    no!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 5) yy))
                )
            )
        )
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 5) yy))
                )
            )
        )
    )
}

#[test]
fn yes_lambda6() {
    yes!(
        (declare-const a Fun)
        (axiom (= a (lambda ((x Int)) (+ x 1))))
        (declare-const b Fun)
        (axiom (= b (lambda ((x Int)) (+ x 1))))
        (check-valid
            (assert (= a b))
        )
    )
}

#[test]
fn no_lambda6() {
    no!(
        (declare-const a Fun)
        (axiom (= a (lambda ((x Int)) (+ x 1))))
        (declare-const b Fun)
        (axiom (= b (lambda ((x Int)) (+ x 2))))
        (check-valid
            (assert (= a b))
        )
    )
}

#[test]
fn yes_lambda_trigger1() {
    yes!(
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Bool)
        (declare-const lf Fun)
        (declare-const lg Fun)
        (declare-const i Int)
        // (axiom (= lf (lambda ((x Int)) (f x)))) // fails without the trigger
        (axiom (= lf (lambda ((x Int)) (!
            (f x)
            :pattern ((f x))
        ))))
        (axiom (= lg (lambda ((x Int)) (g x))))
        (declare-fun enslemma (Fun Fun) Bool)
        (axiom (forall ((x Int)) (!
            (=> (apply Bool lf x) (apply Bool lg x))
            :pattern ((apply Bool lf x))
            :pattern ((apply Bool lg x))
        )))
        (check-valid (block
            (assume (f i))
            (assert (g i))
        ))
    )
}

#[test]
fn yes_lambda_trigger2() {
    yes!(
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Bool)
        (declare-const lf Fun)
        (declare-const lg Fun)
        (declare-const i Int)
        // (axiom (= lf (lambda ((x Int)) (f x)))) // fails without the trigger
        (axiom (= lf (lambda ((x Int)) (!
            (f x)
            :pattern ((f x))
        ))))
        (axiom (= lg (lambda ((x Int)) (g x))))
        (declare-fun enslemma (Fun Fun) Bool)
        (axiom (forall ((fn1 Fun) (fn2 Fun)) (!
            (= (enslemma fn1 fn2)
                (forall ((x Int)) (!
                    (=> (apply Bool fn1 x) (apply Bool fn2 x))
                    :pattern ((apply Bool fn1 x))
                    :pattern ((apply Bool fn2 x))
                )))
            :pattern ((enslemma fn1 fn2))
        )))
        (check-valid (block
            (assume (enslemma lf lg))
            (assume (f i))
            (assert (g i))
        ))
    )
}

#[test]
fn yes_choose1() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 3))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (!
                    (f x x)
                    :pattern ((f x x))
                ) x)
                ))
                (f a a)
                )
            )
        )
    )
}

#[test]
fn yes_choose1_2() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 3))
        (check-valid
            (assert
                (let (( a (choose ((x Int) (y Int)) (!
                        (and (f x y) (= x y))
                        :pattern ((f x y))
                    ) (+ x y))
                    ))
                    (f (div a 2) (div a 2))
                )
            )
        )
    )
}

#[test]
fn no_choose1() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (!
                        (f x x)
                        :pattern ((f x x))
                    ) x) ))
                    (f a a)
                )
            )
        )
    )
}

#[test]
fn no_choose1_2() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int) (y Int)) (!
                        (and (f x y) (= x y))
                        :pattern ((f x y))
                    ) (+ x y)) ))
                    (f (div a 2) (div a 2))
                )
            )
        )
    )
}

#[test]
fn yes_choose2() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 3))
        (check-valid
            (assert
                (let (( a
                        (choose ((x Int))
                            (!
                                (f x x)
                                :pattern ((f x x))
                            )
                            x
                        )
                    ))
                    (f a a)
                )
            )
        )
    )
}

#[test]
fn no_choose2() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a
                        (choose ((x Int))
                            (!
                                (f x x)
                                :pattern ((f x x))
                            )
                            x
                        )
                    ))
                    (f a a)
                )
            )
        )
    )
}

#[test]
fn yes_choose3() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (!
                        (f x 4)
                        :pattern ((f x 4))
                    ) x)
                ))
                (f a 4)
                )
            )
        )
    )
}

#[test]
fn no_choose3() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (f x 3) x) ))
                    (f a 3)
                )
            )
        )
    )
}

#[test]
fn yes_choose4() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert (=
                (choose ((x Int)) (f x 4) x)
                (choose ((x Int)) (f x (+ 2 2)) x)
            ))
        )
    )
}

#[test]
fn no_choose4() {
    no!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert (=
                (choose ((x Int)) (f x 5) x)
                (choose ((x Int)) (f x (+ 2 2)) x)
            ))
        )
    )
}

#[test]
fn yes_choose5() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (let (( g
                        (lambda ((m Int))
                            (choose ((x Int)) (f x (+ m 1)) x)
                        )
                    ))
                    (=
                        (apply Int g 4)
                        (apply Int g (+ 2 2))
                    )
                )
            )
        )
    )
}

#[test]
fn no_choose5() {
    no!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (let (( g
                        (lambda ((m Int))
                            (choose ((x Int)) (f x (+ m 1)) x)
                        )
                    ))
                    (=
                        (apply Int g 5)
                        (apply Int g (+ 2 2))
                    )
                )
            )
        )
    )
}

#[test]
fn yes_partial_order() {
    yes!(
        (declare-sort X 0)
        (declare-const c1 X)
        (declare-const c2 X)
        (declare-const c3 X)
        (check-valid
            (axiom ((_ partial-order 77) c1 c2))
            (axiom ((_ partial-order 77) c2 c3))
            (assert ((_ partial-order 77) c1 c3))
        )
    )
}

#[test]
fn no_partial_order() {
    no!(
        (declare-sort X 0)
        (declare-const c1 X)
        (declare-const c2 X)
        (declare-const c3 X)
        (check-valid
            (axiom ((_ partial-order 77) c1 c2))
            (axiom ((_ partial-order 76) c2 c3))
            (assert ((_ partial-order 77) c1 c3))
        )
    )
}

#[test]
fn datatype_field_update_pass() {
    yes!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int)))))
        (check-valid
            (declare-var a A)
            (block
                (assign a ((_ update-field A_A_u) a 3))
                (assert (= (A_A_u a) 3))
            )
        )
    )
}

#[test]
fn datatype_field_update_ill_typed() {
    untyped!(
        (declare-datatypes ((X 0)) (((X_X (X_X_u Int)))))
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int)))))
        (check-valid
            (declare-var a A)
            (declare-const x X)
            (block
                (assign a ((_ update-field A_A_u) a x))
                (assert (= (A_A_u a) 3))
            )
        )
    )
}

#[test]
fn datatype_field_update2() {
    no!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int)))))
        (check-valid
            (declare-var a A)
            (block
                (assign a ((_ update-field A_A_u) a 3))
                (assert (= (A_A_u a) 4))
            )
        )
    )
}

#[test]
fn datatype_field_update3() {
    yes!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int) (A_A_v Int)))))
        (check-valid
            (declare-var a A)
            (block
                (assign a ((_ update-field A_A_u) a 3))
                (assert (= (A_A_u a) 3))
            )
        )
    )
}

#[test]
fn datatype_field_update4() {
    no!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int) (A_A_v Int)))))
        (check-valid
            (declare-var a A)
            (block
                (assign a ((_ update-field A_A_u) a 3))
                (assert (= (A_A_u a) 4))
            )
        )
    )
}

#[test]
fn nested_datatype_field_update_pass() {
    yes!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int)))))
        (declare-datatypes ((B 0)) (((B_B (B_B_a A)))))
        (check-valid
            (declare-var b B)
            (block
                (assign b ((_ update-field B_B_a) b ((_ update-field A_A_u) (B_B_a b) 3)))
                (assert (= (A_A_u (B_B_a b)) 3))
            )
        )
    )
}

#[test]
fn nested_datatype_field_update_pass2() {
    yes!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int) (A_A_v Int)))))
        (declare-datatypes ((B 0)) (((B_B (B_B_a1 A) (B_B_a2 A)))))
        (check-valid
            (declare-var b B)
            (block
                (assign b ((_ update-field B_B_a1) b ((_ update-field A_A_u) (B_B_a1 b) 3)))
                (assert (= (A_A_u (B_B_a1 b)) 3))
            )
        )
    )
}

#[test]
fn nested_datatype_field_update_fail() {
    no!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int)))))
        (declare-datatypes ((B 0)) (((B_B (B_B_a A)))))
        (check-valid
            (declare-var b B)
            (block
                (assign b ((_ update-field B_B_a) b ((_ update-field A_A_u) (B_B_a b) 3)))
                (assert (= (A_A_u (B_B_a b)) 4))
            )
        )
    )
}

#[test]
fn accessor_identifying_1() {
    untyped!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int)))))
        (declare-fun f (A) Int )
        (check-valid
            (declare-var a A)
            (block
                (assign a ((_ update-field f) a 3))
                (assert (= (A_A_u a) 4))
            )
        )
    )
}

#[test]
fn accessor_identifying_2() {
    untyped!(
        (declare-datatypes ((A 0)) (((A_A (A_A_u Int)))))
        (declare-datatypes ((B 0)) (((B_B (B_B_u Int)))))
        (check-valid
            (declare-var a A)
            (block
                (assign a ((_ update-field B_B_u) a 3))
                (assert (= (A_A_u a) 4))
            )
        )
    )
}

/// Parse a `check-valid` written with assert ids, print it, and require the
/// printed form to read back to the same nodes: the `.air` log must carry
/// the ids and stay a valid AIR input.
#[test]
fn assert_id_roundtrip() {
    let text = r#"(check-valid
  (declare-const x Int)
  (axiom hyp_0 (> x 3))
  (axiom hyp_1 (! (>= x 0) :named req_nonneg))
  (axiom (< x 100))
  (block
    (assume (> x 3))
    (assert aid_2 ("assertion failed") () (> x 2))
    (assert aid_5_1 ("assertion failed") () (location aid_5_1_0 ("nested") () (>= x 0)))
    (assert ("no id keeps the old form") () (> x 1))
  ))"#;
    // (a bare `(assert e)` is left out: it reads back with an empty message,
    // which prints as `("")`, a pre-existing asymmetry unrelated to ids)
    let mut sise_parser = sise::Parser::new(text);
    let node = sise::parse_tree(&mut sise_parser).expect("sise");
    let message_interface = std::sync::Arc::new(crate::messages::AirMessageInterface {});
    let parser = Parser::new(message_interface.clone());
    let commands = parser.nodes_to_commands(std::slice::from_ref(&node)).expect("parses");
    assert_eq!(commands.len(), 1);
    let query = match &*commands[0] {
        CommandX::CheckValid(query) => query.clone(),
        other => panic!("expected check-valid, got {:?}", other),
    };
    // the hypothesis tags arrived on the local axioms
    let tags: Vec<Option<String>> = query
        .local
        .iter()
        .filter_map(|d| match &**d {
            crate::ast::DeclX::Axiom(a) => Some(a.tag.as_ref().map(|t| t.to_symbol())),
            _ => None,
        })
        .collect();
    assert_eq!(
        tags,
        vec![Some("hyp_0".to_string()), Some("hyp_1".to_string()), None],
        "tags read back from the axiom declarations"
    );
    // the ids arrived
    match &*query.assertion {
        crate::ast::StmtX::Block(stmts) => {
            let ids: Vec<Option<Vec<u64>>> = stmts
                .iter()
                .map(|s| match &**s {
                    crate::ast::StmtX::Assert(id, _, _, _) => id.as_ref().map(|i| (**i).clone()),
                    _ => None,
                })
                .collect();
            assert_eq!(
                ids,
                vec![None, Some(vec![2]), Some(vec![5, 1]), None],
                "ids read back from the assert statements"
            );
        }
        other => panic!("expected block, got {:?}", other),
    }
    // and print back to exactly what was read
    let printer = crate::printer::Printer::new(message_interface.clone(), false, SmtSolver::Cvc5);
    let printed = printer.query_to_node(&query);
    assert_eq!(printed, node);
}

/// cvc5's `(get-info :matching-loops)` reply, as it prints it: one loop per
/// line after the header.
#[test]
fn matching_loops_reply_parses() {
    let lines: Vec<String> = [
        "(:matching-loops (:rounds 10 :instantiations 12 :dropped 0 :max-inst-rounds true :loops (",
        "(loop :qid |user_f_grows_3| :confidence high :growth linear-depth :edges confirmed \
         :stable true :instantiations 10 :rounds 10 :first-round 1 :last-round 10 :chain 10 \
         :self-fed 9 :depth-per-rung 1.00 :depth-per-round 1.00 :fanout-per-round 1.00 \
         :via () :trigger ((f x)) :context ((g _0)) :shape ((f _0)) :step ((f (g _0))) \
         :ladder (((f a)) ((f (g a))) ((f (g (g a)))) ((f (g (g (g a)))))) :ladder-length 10 \
         :per-round (1 1 1 1 1 1 1 1 1 1)))))",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    let info = crate::smt_verify::parse_matching_loops_lines(&lines);
    assert!(info.unparsed.is_empty(), "{:?}", info.unparsed);
    assert_eq!((info.rounds, info.instantiations, info.max_inst_rounds), (10, 12, true));
    assert_eq!(info.loops.len(), 1);
    let l = &info.loops[0];
    assert_eq!(l.qid, "user_f_grows_3");
    assert_eq!((l.confidence.as_str(), l.growth.as_str()), ("high", "linear-depth"));
    assert!(l.edges_confirmed && l.stable);
    assert_eq!((l.chain, l.self_fed, l.ladder_length), (10, 9, 10));
    assert_eq!(l.depth_per_round, 1.0);
    assert_eq!(l.trigger, vec!["(f x)"]);
    assert_eq!(l.context, vec!["(g _0)"]);
    assert_eq!(l.shape, vec!["(f _0)"]);
    assert_eq!(l.step, vec!["(f (g _0))"]);
    assert_eq!(l.ladder.len(), 4);
    assert_eq!(l.ladder[1], vec!["(f (g a))"]);
    assert_eq!(l.per_round.len(), 10);
    // no loops; and a reply of another shape is kept, not failed on
    let info = crate::smt_verify::parse_matching_loops_lines(&vec![
        "(:matching-loops (:rounds 2 :instantiations 3 :dropped 0 :max-inst-rounds false :loops ()))"
            .to_string(),
    ]);
    assert!(info.loops.is_empty() && info.unparsed.is_empty());
    let info = crate::smt_verify::parse_matching_loops_lines(&vec!["(error \"no\")".to_string()]);
    assert_eq!(info.unparsed, vec!["(error \"no\")".to_string()]);
    // a quoted symbol sise cannot read bare, a bar inside a string literal,
    // and a term broken across lines: the reply still parses, terms one line
    let info = crate::smt_verify::parse_matching_loops_lines(&vec![
        "(:matching-loops (:rounds 3 :instantiations 3 :dropped 0 :max-inst-rounds false :loops ("
            .to_string(),
        "(loop :qid |odd name| :confidence low :growth bounded :edges unconfirmed :stable false \
         :via (|odd name|) :trigger ((str.++ s \"a|b\")) :shape ((f\n   (g _0))) :ladder-length 0))))"
            .to_string(),
    ]);
    assert!(info.unparsed.is_empty(), "{:?}", info.unparsed);
    let l = &info.loops[0];
    assert_eq!((l.qid.as_str(), l.via.clone()), ("|odd name|", vec!["|odd name|".to_string()]));
    assert_eq!(l.trigger, vec!["(str.++ s \"a|b\")"]);
    assert_eq!(l.shape, vec!["(f (g _0))"]);
    // `:fanout-per-step` beside `:fanout-per-round`, and one context per
    // class of growing subterm (BasisResearch/cvc5#3 since ea27199)
    let info = crate::smt_verify::parse_matching_loops_lines(&vec![
        "(:matching-loops (:rounds 10 :instantiations 31 :dropped 0 :max-inst-rounds true :loops ("
            .to_string(),
        "(loop :qid |user_f_branches_1| :confidence high :growth exponential-fanout \
         :edges confirmed :stable true :fanout-per-round 1.41 :fanout-per-step 2.00 \
         :context ((r _0) (l _0)) :ladder-length 5))))"
            .to_string(),
    ]);
    assert!(info.unparsed.is_empty(), "{:?}", info.unparsed);
    let l = &info.loops[0];
    assert_eq!((l.fanout_per_round, l.fanout_per_step), (1.41, 2.0));
    assert_eq!(l.context, vec!["(r _0)", "(l _0)"]);
}

/// The extra lines provenance mode adds to a check-sat batch: instantiation
/// dump forms and the tags-only sources reply, in the order cvc5 prints them.
#[test]
fn provenance_reply_parses() {
    let lines: Vec<String> = [
        "(instantiations prelude_unbox_box_int",
        "  ( 2 )",
        "  ( x! )",
        ")",
        "(instantiations user_fixture__check_4",
        "  ( (I 2) )",
        ")",
        "((ax_fixture!ax_f_nonneg.) (hyp_1) (hyp_3) (query hyp_2 hyp_0) (query))",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    let info = crate::smt_verify::parse_provenance_lines(&lines);
    assert_eq!(
        info.instantiations,
        vec![
            ("prelude_unbox_box_int".to_string(), vec!["(2)".to_string(), "(x!)".to_string()]),
            ("user_fixture__check_4".to_string(), vec!["((I 2))".to_string()]),
        ]
    );
    assert_eq!(info.sources.len(), 5);
    assert_eq!(info.sources[3], vec!["query", "hyp_2", "hyp_0"]);
    assert!(info.unparsed.is_empty());
    // no instantiations: cvc5 prints `none`; an empty reply is empty
    let info =
        crate::smt_verify::parse_provenance_lines(&vec!["none".to_string(), "()".to_string()]);
    assert!(info.instantiations.is_empty() && info.sources.is_empty() && info.unparsed.is_empty());
    let info = crate::smt_verify::parse_provenance_lines(&vec![]);
    assert!(info.instantiations.is_empty() && info.sources.is_empty());
    // something unforeseen is kept, not failed on
    let info = crate::smt_verify::parse_provenance_lines(&vec!["(surprise 1 2)".to_string()]);
    assert_eq!(info.unparsed, vec!["(surprise 1 2)".to_string()]);
}

/// cvc5's `(get-info :incomplete-culprits)` reply: plain symbols, and symbols
/// it had to quote.
#[test]
fn incomplete_culprits_reply_parses() {
    let parse = crate::smt_verify::parse_incomplete_culprits;
    assert_eq!(
        parse("(:incomplete-culprits (user_lib__f_4 |also never matched| prelude_box_unbox))"),
        vec!["user_lib__f_4", "also never matched", "prelude_box_unbox"]
    );
    assert!(parse("(:incomplete-culprits ())").is_empty());
    // an unterminated quote ends the list rather than inventing a name
    assert_eq!(parse("(:incomplete-culprits (a |b))"), vec!["a"]);
    assert!(parse("unsupported").is_empty());
}

#[test]
fn parse_nl_frontier_reply() {
    // the shape cvc5's (get-info :nl-frontier) prints after a budget runs out
    let f = crate::smt_verify::parse_nl_frontier(
        "(:nl-frontier (:result unknown :reason resourceout :enabled true :checks 40 \
         :rounds 38 :punts 0 :last lemma :atoms (\
         (:atom (* x y) :kind product :current true :rounds 12 :value 5 :from-args -6 \
         :lower (:value 0 :strict false :fixed true) \
         :args ((:term x :value 2 :lower (:value 0 :strict false :fixed true)) \
         (:term |y%1| :value -1/3 :upper (:value 10 :strict true :fixed false))) \
         :hosts ((:in input :term (Mul x |y%1|) :tags (query hyp_2)) \
         (:in instance :term (Mul x |y%1|) :qid prelude_mul :count 3)))) \
         :omitted 0 :truncated false))",
    );
    assert!(f.unparsed.is_none(), "{:?}", f.unparsed);
    assert_eq!(
        (f.result.as_str(), f.reason.as_str(), f.last.as_str()),
        ("unknown", "resourceout", "lemma")
    );
    assert_eq!((f.enabled, f.checks, f.rounds, f.punts, f.omitted), (true, 40, 38, 0, 0));
    let a = &f.atoms[0];
    assert_eq!(
        (a.atom.as_str(), a.kind.as_str(), a.current, a.rounds),
        ("(* x y)", "product", true, 12)
    );
    assert_eq!((a.value.as_str(), a.from_args.as_str()), ("5", "-6"));
    assert_eq!(a.args[1].value, "-1/3");
    assert!(a.lower.as_ref().is_some_and(|b| b.value == "0" && !b.strict && b.fixed));
    assert!(a.upper.is_none());
    // quoted symbols lose their bars
    assert_eq!(a.args[1].term, "y%1");
    assert!(a.args[1].upper.as_ref().is_some_and(|b| b.value == "10" && b.strict && !b.fixed));
    assert_eq!(a.hosts.len(), 2);
    assert!(a.hosts[0].input && a.hosts[0].tags == vec!["query", "hyp_2"]);
    assert_eq!(a.hosts[0].term, "(Mul x y%1)");
    assert!(!a.hosts[1].input && a.hosts[1].qid.as_deref() == Some("prelude_mul"));
    assert_eq!(a.hosts[1].count, 3);

    // nothing recorded; a solver without the key or anything unforeseen is kept whole
    let f = crate::smt_verify::parse_nl_frontier(
        "(:nl-frontier (:result unsat :reason none :enabled true :checks 0 :rounds 0 \
         :punts 0 :last none :atoms () :omitted 0 :truncated false))",
    );
    assert!(f.unparsed.is_none() && f.atoms.is_empty() && f.result == "unsat");
    let bad = "(:nl-frontier (:result sat :atoms ((:atom (* x y) :rounds many))))";
    assert_eq!(crate::smt_verify::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
    let bad = "(:nl-frontier unsupported)";
    assert_eq!(crate::smt_verify::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
    // a key without a value is malformed, at any depth
    let bad = "(:nl-frontier (:result sat :checks))";
    assert_eq!(crate::smt_verify::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
    let bad = "(:nl-frontier (:result sat :atoms ((:atom (* x y) :kind))))";
    assert_eq!(crate::smt_verify::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
    // a quoted symbol that is not one word keeps its bars
    let f = crate::smt_verify::parse_nl_frontier(
        "(:nl-frontier (:result sat :atoms ((:atom (* x |a b|) :args ((:term |a b| :value 3)) \
         :hosts ((:in input :term (Mul x |a b|) :tags (query)))))))",
    );
    assert!(f.unparsed.is_none(), "{:?}", f.unparsed);
    assert_eq!(f.atoms[0].atom, "(* x |a b|)");
    assert_eq!(f.atoms[0].args[0].term, "|a b|");
    assert_eq!(f.atoms[0].hosts[0].term, "(Mul x |a b|)");
}

#[test]
fn parse_difficulty_gradient_reply() {
    // cvc5's reply to the regression get-info-difficulty-gradient.smt2
    let g = crate::smt_verify::parse_difficulty_gradient(
        "(:difficulty-gradient (:result unsat :difficulty true :core true :rows (\
         (:tags (ax_f) :difficulty 1 :in-core true) \
         (:tags (query_0) :difficulty 1 :in-core true) \
         (:tags (hyp_a |hyp%b|) :difficulty 0 :in-core false)) \
         :untagged (:asserted 1 :difficulty 0 :in-core 0) :unmatched-difficulty 0))",
    );
    assert!(g.unparsed.is_none(), "{:?}", g.unparsed);
    assert_eq!((g.result.as_str(), g.difficulty, g.core, g.rows.len()), ("unsat", true, true, 3));
    assert_eq!(g.rows[0].tags, vec!["ax_f".to_string()]);
    assert_eq!((g.rows[0].difficulty, g.rows[0].in_core), (1, Some(true)));
    // merged assertions carry several tags; quoted symbols lose their bars
    assert_eq!(g.rows[2].tags, vec!["hyp_a".to_string(), "hyp%b".to_string()]);
    assert_eq!(g.rows[2].in_core, Some(false));
    assert_eq!((g.untagged_asserted, g.untagged_in_core, g.unmatched_difficulty), (1, Some(0), 0));

    // a quoted symbol may hold spaces and quotes
    let g = crate::smt_verify::parse_difficulty_gradient(
        "(:difficulty-gradient (:result sat :difficulty true :core false :rows (\
         (:tags (|a \"b\" c|) :difficulty 2)) :untagged (:asserted 0 :difficulty 0) \
         :unmatched-difficulty 0))",
    );
    assert!(g.unparsed.is_none(), "{:?}", g.unparsed);
    assert_eq!(g.rows[0].tags, vec!["a \"b\" c".to_string()]);

    // no core outside unsat; a count beyond u64 saturates
    let g = crate::smt_verify::parse_difficulty_gradient(
        "(:difficulty-gradient (:result unknown :difficulty true :core false :rows (\
         (:tags (ax_f) :difficulty 123456789012345678901234567890)) \
         :untagged (:asserted 2 :difficulty 7) :unmatched-difficulty 3))",
    );
    assert!(g.unparsed.is_none() && !g.core);
    assert_eq!((g.rows[0].difficulty, g.rows[0].in_core), (u64::MAX, None));
    assert_eq!((g.untagged_difficulty, g.untagged_in_core, g.unmatched_difficulty), (7, None, 3));

    // a solver without the key, or anything unforeseen, is kept whole
    let g = crate::smt_verify::parse_difficulty_gradient("(:difficulty-gradient unsupported)");
    assert_eq!(g.unparsed.as_deref(), Some("(:difficulty-gradient unsupported)"));
    let bad = "(:difficulty-gradient (:result sat :rows ((:tags (a) :difficulty many))))";
    assert_eq!(crate::smt_verify::parse_difficulty_gradient(bad).unparsed.as_deref(), Some(bad));
}

#[test]
fn replayed_scope_reuses_generated_names() {
    // A resident session rebuilds a popped query prefix by replaying its
    // declarations. The replay must name AIR's generated symbols as the first
    // pass did, because instantiation certificates refer to formulas that
    // mention them.
    let message_interface = std::sync::Arc::new(crate::messages::AirMessageInterface {});
    let mut nodes = Vec::new();
    macro_push_node(
        &mut nodes,
        node!((axiom (= 10 (apply Int (lambda ((x Int) (y Int)) (+ x y 5)) 2 3)))),
    );
    let commands = Parser::new(message_interface.clone()).nodes_to_commands(&nodes).unwrap();
    let CommandX::Global(decl) = &*commands[0] else { panic!("expected a declaration") };
    let mut air_context = crate::context::Context::new(message_interface, SmtSolver::Z3);
    let scope = |air_context: &mut crate::context::Context| {
        air_context.push();
        air_context.global(decl).unwrap();
        air_context.pop();
        String::from_utf8(air_context.smt_log.take_pipe_data()).unwrap()
    };
    let first = scope(&mut air_context);
    let second = scope(&mut air_context);
    assert!(first.contains("%%lambda%%0"), "{}", first);
    assert!(second.contains("%%lambda%%0") && !second.contains("%%lambda%%1"), "{}", second);
}

#[test]
fn type_error_in_query_closes_its_name_scope() {
    // A query that fails to type-check must close the name scope it opened.
    // Otherwise the next pop closes that scope instead of the caller's, and a
    // lambda declared in the caller's scope stays cached after the solver
    // drops its declaration, so declaring it again emits nothing.
    let message_interface = std::sync::Arc::new(crate::messages::AirMessageInterface {});
    let mut nodes = Vec::new();
    macro_push_node(
        &mut nodes,
        node!((axiom (= 10 (apply Int (lambda ((x Int) (y Int)) (+ x y 5)) 2 3)))),
    );
    macro_push_node(&mut nodes, node!((check-valid (assert (forall ((x Int)) (+ x true))))));
    let commands = Parser::new(message_interface.clone()).nodes_to_commands(&nodes).unwrap();
    let CommandX::Global(decl) = &*commands[0] else { panic!("expected a declaration") };
    let mut air_context = crate::context::Context::new(message_interface.clone(), SmtSolver::Z3);
    air_context.push();
    air_context.global(decl).unwrap();
    let result =
        air_context.command(&*message_interface, &Reporter {}, &commands[1], Default::default());
    assert!(matches!(result, ValidityResult::TypeError(_)), "{:?}", result);
    air_context.pop();
    let _ = air_context.smt_log.take_pipe_data();
    air_context.global(decl).unwrap();
    let again = String::from_utf8(air_context.smt_log.take_pipe_data()).unwrap();
    assert!(again.contains("(declare-fun %%lambda%%0"), "{}", again);
}

#[test]
fn type_error_in_declaration_closes_its_binder_scope() {
    // A declaration whose type error is inside a binder must close the
    // binder's typing scope. Otherwise the next pop leaves the typing scopes
    // one deeper than the name maps, which lowering the next lambda asserts
    // against.
    let message_interface = std::sync::Arc::new(crate::messages::AirMessageInterface {});
    let mut nodes = Vec::new();
    macro_push_node(&mut nodes, node!((axiom (forall ((x Int)) (+ x true)))));
    macro_push_node(
        &mut nodes,
        node!((axiom (= 10 (apply Int (lambda ((x Int) (y Int)) (+ x y 5)) 2 3)))),
    );
    let commands = Parser::new(message_interface.clone()).nodes_to_commands(&nodes).unwrap();
    let CommandX::Global(ill_typed) = &*commands[0] else { panic!("expected a declaration") };
    let CommandX::Global(lambda) = &*commands[1] else { panic!("expected a declaration") };
    let mut air_context = crate::context::Context::new(message_interface, SmtSolver::Z3);
    air_context.push();
    assert!(air_context.global(ill_typed).is_err());
    air_context.pop();
    air_context.global(lambda).unwrap();
}

#[test]
fn parse_inst_pressure_reply() {
    let info = crate::smt_verify::parse_inst_pressure(
        "(:inst-pressure (:rounds 3 :refutation true :quantifiers (\
         (user_f_1 :instantiations 5 :duplicate-eq 2 :duplicate-ent 1 :duplicate-lemma 0 \
         :conflict 1 :propagate 0 :first-round 0 :last-round 2 :refutation 1) \
         (|user%g| :instantiations 0 :duplicate-eq 4 :duplicate-ent 0 :duplicate-lemma 0 \
         :conflict 0 :propagate 0 :refutation 0) \
         (quant_0 :named false :instantiations 1 :duplicate-eq 0 :duplicate-ent 0 \
         :duplicate-lemma 0 :conflict 0 :propagate 1 :first-round 1 :last-round 1 \
         :refutation 0))))",
    );
    assert!(info.unparsed.is_none(), "{:?}", info.unparsed);
    assert_eq!((info.rounds, info.refutation, info.quantifiers.len()), (3, true, 3));
    let f = &info.quantifiers[0];
    assert_eq!(f.qid, "user_f_1");
    assert!(f.named);
    assert_eq!(
        (f.instantiations, f.duplicate_eq, f.duplicate_ent, f.duplicate_lemma),
        (5, 2, 1, 0)
    );
    assert_eq!(
        (f.conflict, f.first_round, f.last_round, f.refutation),
        (1, Some(0), Some(2), Some(1))
    );
    // only duplicates: no rounds; quoted symbols lose their bars
    let q = &info.quantifiers[1];
    assert_eq!((q.qid.as_str(), q.first_round, q.duplicate_eq), ("user%g", None, 4));
    let u = &info.quantifiers[2];
    assert_eq!((u.qid.as_str(), u.named, u.propagate), ("quant_0", false, 1));

    // no quantifier instantiated; no refutation counts outside proof mode
    let info = crate::smt_verify::parse_inst_pressure(
        "(:inst-pressure (:rounds 0 :refutation false :quantifiers ()))",
    );
    assert!(info.unparsed.is_none() && info.quantifiers.is_empty() && !info.refutation);
    // a solver without the key, or anything unforeseen, is kept whole
    let info = crate::smt_verify::parse_inst_pressure("(:inst-pressure unsupported)");
    assert_eq!(info.unparsed.as_deref(), Some("(:inst-pressure unsupported)"));
}

#[test]
fn parse_inst_pressure_symbols() {
    let row = |qid: &str| {
        format!(
            "(:inst-pressure (:rounds 1 :refutation false :quantifiers (({} :instantiations 1 \
             :duplicate-eq 0 :duplicate-ent 0 :duplicate-lemma 0 :conflict 0 :propagate 0 \
             :first-round 0 :last-round 0))))",
            qid
        )
    };
    let qids = |line: &str| {
        let info = crate::smt_verify::parse_inst_pressure(line);
        assert!(info.unparsed.is_none(), "{:?}", info.unparsed);
        info.quantifiers.into_iter().map(|q| q.qid).collect::<Vec<_>>()
    };
    // a simple symbol may hold characters sise's atoms lack
    assert_eq!(qids(&row("a^b")), vec!["a^b"]);
    // a quoted one may hold anything but a bar, spaces and quotes included
    assert_eq!(qids(&row("|a b|")), vec!["a b"]);
    assert_eq!(qids(&row("|say \"hi\"|")), vec!["say \"hi\""]);
    assert_eq!(qids(&row("||")), vec![""]);

    // unbalanced, trailing, or cut short: kept whole
    for line in [
        "(:inst-pressure (:rounds 1 :refutation false :quantifiers ((a :instantiations 1)))",
        "(:inst-pressure (:rounds 1)) x",
        "(:inst-pressure (:rounds 1 :refutation false :quantifiers ((|a :instantiations 1))))",
    ] {
        let info = crate::smt_verify::parse_inst_pressure(line);
        assert_eq!(info.unparsed.as_deref(), Some(line));
    }
    // a malformed row is reported, the others kept
    let info = crate::smt_verify::parse_inst_pressure(
        "(:inst-pressure (:rounds 2 :refutation false :quantifiers ((ok :instantiations 1) \
         (bad :instantiations x))))",
    );
    assert!(info.unparsed.is_some());
    assert_eq!(info.quantifiers.len(), 1);
}
