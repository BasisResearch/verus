//! Test host for `vstd::contrib::dyncov`; see Cargo.toml.
#![allow(dead_code)]

pub mod contrib {
    pub mod dyncov {
        pub use crate::runtime::*;
    }
}

#[path = "../../../vstd/contrib/dyncov/mod.rs"]
pub mod runtime;
