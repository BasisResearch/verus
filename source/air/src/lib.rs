pub mod air_observer;
pub mod ast;
pub mod ast_util;
pub mod bisect;
pub mod context;
pub mod emitter;
pub mod focus;
pub mod inst_graph;
pub mod instantiations;
pub mod messages;
pub mod model;
pub mod parser;
pub mod profiler;
pub mod query_result_observer;
pub mod remove_asserts;
pub mod scope_map;
pub mod smt_process;
pub mod speculate;
pub mod twin;

#[macro_use]
pub mod printer;
pub mod scaffold;

mod block_to_assert;
pub use block_to_assert::lower_query;
mod closure;
pub mod def;
mod smt_verify;
mod tests;
mod typecheck;
mod util;
mod var_to_const;
pub use var_to_const::GoalScope;
pub mod visitor;

#[cfg(feature = "singular")]
pub mod singular_manager;
