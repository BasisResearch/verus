pub use verus_builtin_macros::auto_spec;
pub use verus_builtin_macros::{make_spec_type, self_view};
pub use verus_builtin_macros::{set_build, set_build_debug};
pub mod exec_spec;
#[cfg(all(feature = "alloc", feature = "std"))]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub mod dyncov;
