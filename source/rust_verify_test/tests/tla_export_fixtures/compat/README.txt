The golden files are the unmodified parent-lane exports at commit
6fc818cad8e20a29dc50432c8b8a7b0a49b91253. They were generated with the same crate name (test_crate) as the test
harness. Only the checkout-dependent source path (@SOURCE@) is normalized. The regression
compares every byte of the four generated TLA/configuration files for all
six examples/tla Rust fixtures and the pinned Raft model.

raft.rs is copied verbatim from the local toyDB Raft safety model,
trace-arm-eval/toydb/src/raft/safety.rs, on 2026-10-07. Its upstream
MIT/Apache licenses are included. It is exported with --no-verify; the
regression checks the exporter, not the model's proof bodies.
