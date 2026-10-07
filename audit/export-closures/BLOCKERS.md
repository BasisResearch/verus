# Remaining cumulative campaign blockers

Locations below are emitted by the exporter or compiler; repeated refusals are counted rather than hidden. Timeouts have no completed refusal report and therefore no inferred source-level cause.

## anvil/Cluster-adapter

- 1× **closure value `model` used other than in an application**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/kubernetes_cluster/spec/cluster.rs:133:25: 133:30 (#0)` (in `cluster_adapter::adapter::init`).
- 1× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/kubernetes_cluster/spec/external/state_machine.rs:41:24: 41:38 (#0)` (in `cluster_adapter::adapter::init`).
- 15× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:44:26: 44:116 (#0)` (in `cluster_adapter::adapter::next`).
- 15× **choose without a representable domain**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:45:32: 45:136 (#0)` (in `cluster_adapter::adapter::next`).
- 15× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:48:35: 48:71 (#0)` (in `cluster_adapter::adapter::next`).
- 15× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:48:75: 48:111 (#0)` (in `cluster_adapter::adapter::next`).

## anvil/sub_api

- 10× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/kubernetes_cluster/spec/api_server/state_machine.rs:88:45: 88:100 (#0)` (in `sub_adapters2::sub_api::next`).
- 10× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/kubernetes_cluster/spec/api_server/state_machine.rs:105:45: 105:104 (#0)` (in `sub_adapters2::sub_api::next`).
- 1× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/kubernetes_cluster/spec/api_server/state_machine.rs:196:45: 196:98 (#0)` (in `sub_adapters2::sub_api::next`).
- 1× **ordering comparison of chars**, `vstd/utf8.rs:1103:40: 1103:79 (#0)` (in `vstd::utf8::is_ascii_chars`).
- 20× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/kubernetes_cluster/spec/api_server/state_machine.rs:148:45: 148:88 (#0)` (in `sub_adapters2::sub_api::next`).
- 16× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/kubernetes_cluster/spec/api_server/state_machine.rs:172:45: 172:101 (#0)` (in `sub_adapters2::sub_api::next`).

## anvil/sub_api_sm

- 2× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:44:26: 44:116 (#0)` (in `sub_adapters2::sub_api_sm::next`).
- 2× **choose without a representable domain**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:45:32: 45:136 (#0)` (in `sub_adapters2::sub_api_sm::next`).
- 2× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:48:35: 48:71 (#0)` (in `sub_adapters2::sub_api_sm::next`).
- 2× **application of a spec_fn value that does not reduce to a closure**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/anvil-verifier_anvil/src/state_machine/state_machine.rs:48:75: 48:111 (#0)` (in `sub_adapters2::sub_api_sm::next`).

## nrkernel/mmu_rl1

- 27× **partial-read analysis exceeds its expansion limit**, `/data/home/kirancodes/Documents/code/verus-research/survey/repos/matthias-brun_verified-nrkernel/page-table/src/spec_t/mmu/rl1.rs:296:21: 296:32 (#0)` (in `lib::spec_t::mmu::rl1::step_WriteNonneg`).
- 27× **partial-read analysis exceeds its expansion limit**, `/data/home/kirancodes/Documents/code/verus-research/survey/repos/matthias-brun_verified-nrkernel/page-table/src/spec_t/mmu/pt_mem.rs:92:9: 127:10 (#0)` (in `lib::spec_t::mmu::rl1::step_WriteNonneg`).
- 27× **partial-read analysis exceeds its expansion limit**, `/data/home/kirancodes/Documents/code/verus-research/survey/repos/matthias-brun_verified-nrkernel/page-table/src/spec_t/mmu/rl1.rs:324:21: 324:31 (#0)` (in `lib::spec_t::mmu::rl1::step_WriteNonpos`).
- 27× **partial-read analysis exceeds its expansion limit**, `/data/home/kirancodes/Documents/code/verus-research/survey/repos/matthias-brun_verified-nrkernel/page-table/src/spec_t/mmu/pt_mem.rs:92:9: 127:10 (#0)` (in `lib::spec_t::mmu::rl1::step_WriteNonpos`).
- 27× **partial-read analysis exceeds its expansion limit**, `/data/home/kirancodes/Documents/code/verus-research/survey/repos/matthias-brun_verified-nrkernel/page-table/src/spec_t/mmu/pt_mem.rs:227:18: 227:22 (#0)` (in `lib::spec_t::mmu::rl1::step_WriteProtect`).
- 27× **partial-read analysis exceeds its expansion limit**, `/data/home/kirancodes/Documents/code/verus-research/survey/repos/matthias-brun_verified-nrkernel/page-table/src/spec_t/mmu/pt_mem.rs:227:31: 227:33 (#0)` (in `lib::spec_t::mmu::rl1::step_WriteProtect`).
- 27× **partial-read analysis exceeds its expansion limit**, `/data/home/kirancodes/Documents/code/verus-research/survey/repos/matthias-brun_verified-nrkernel/page-table/src/spec_t/mmu/pt_mem.rs:85:58: 128:6 (#0)` (in `lib::spec_t::mmu::rl1::step_WriteProtect`).

## nrkernel/mmu_rl2


Export exceeded the original 90-second timeout. No completed report; construct/location unknown.

## nrkernel/mmu_rl3


Export exceeded the original 90-second timeout. No completed report; construct/location unknown.

## nrkernel/os


Export exceeded the original 90-second timeout. No completed report; construct/location unknown.

## splinter/AllocationBetree


compiler_diagnostics:
```text
error[E0659]: `Address` is ambiguous
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBetree_v.rs:95:110
   |
95 |     transition!{ internal_grow(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) {
   |                                                                                                              ^^^^^^^ ambiguous name
   |

error[E0659]: `Address` is ambiguous
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBetree_v.rs:47:48
   |
47 |     pub open spec fn is_fresh(self, addrs: Set<Address>) -> bool
   |                                                ^^^^^^^ ambiguous name
   |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesBetree_v.rs:358:65
    |
358 |     proof fn addr_for_buffer(self, betree_likes: Likes, buffer: Address) -> (addr: Address)
    |                                                                 ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesBetree_v.rs:358:84
    |
358 |     proof fn addr_for_buffer(self, betree_likes: Likes, buffer: Address) -> (addr: Address)
    |                                                                                    ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesBetree_v.rs:378:71
    |
378 |     proof fn tree_buffers_are_closed(self, betree_likes: Likes, addr: Address)
    |                                                                       ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesBetree_v.rs:1094:110
     |
1094 |     transition!{ internal_grow(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) {
     |                                                                                                              ^^^^^^^ ambiguous name
     |

error[E0659]: `Address` is ambiguous
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesBetree_v.rs:1400:133
     |
1400 | ...nkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) { 
     |                                                        ^^^^^^^ ambiguous name
     |

error[E0659]: `Address` is ambiguous
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesBetree_v.rs:1062:48
     |
1062 |     pub open spec fn is_fresh(self, addrs: Set<Address>) -> bool
     |                                                ^^^^^^^ ambiguous name
     |
```

## splinter/AllocationBranchBetree


compiler_diagnostics:
```text
error[E0432]: unresolved import `crate::betree::LinkedBranch_v::Refinement_v`
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranchBetree_v.rs:27:5
   |
27 | use crate::betree::LinkedBranch_v::Refinement_v;
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ no `Refinement_v` in `betree::LinkedBranch_v`


error[E0432]: unresolved import `crate::betree::LinkedBranch_v::Refinement_v`
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranch_v.rs:17:5
   |
17 | use crate::betree::LinkedBranch_v::Refinement_v;
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ no `Refinement_v` in `betree::LinkedBranch_v`
   |

error[E0425]: cannot find function `lemma_values_finite` in this scope
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranchBetree_v.rs:838:9
    |
838 |           lemma_values_finite(post.branch_summary);
    |           ^^^^^^^^^^^^^^^^^^^
    |

error[E0425]: cannot find function `lemma_values_finite` in this scope
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranchBetree_v.rs:965:13
    |
965 |               lemma_values_finite(post.branch_summary);
    |               ^^^^^^^^^^^^^^^^^^^
    |

error[E0425]: cannot find function `lemma_values_finite` in this scope
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranchBetree_v.rs:1159:9
     |
1159 |           lemma_values_finite(root_to_au);
     |           ^^^^^^^^^^^^^^^^^^^
     |

error[E0425]: cannot find function `lemma_values_finite` in this scope
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranchBetree_v.rs:1166:9
     |
1166 |           lemma_values_finite(result);
     |           ^^^^^^^^^^^^^^^^^^^
     |

error[E0425]: cannot find function `lemma_values_finite` in this scope
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranchBetree_v.rs:1455:5
     |
1455 |       lemma_values_finite(branch_summary);
     |       ^^^^^^^^^^^^^^^^^^^
     |

error[E0425]: cannot find function `lemma_values_finite` in this scope
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationBranchBetree_v.rs:1472:5
     |
1472 |       lemma_values_finite(post_summary);
     |       ^^^^^^^^^^^^^^^^^^^
     |
```

## splinter/AllocationCrashAwareJournal


compiler_diagnostics:
```text
error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:64:14
   |
64 |     Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn, |lsn| lsn_au_index[lsn])
   |     -------- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<nat>`, found `FnSpec<(nat,), bool>`
   |     |

error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:82:14
   |
82 |     Map::new(|lsn| start_lsn <= lsn < end_lsn, |lsn| value)
   |     -------- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<nat>`, found `FnSpec<(_,), bool>`
   |     |

error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:130:9
    |
126 | pub open spec(checked) fn au_addrs_past_pointer(ptr: Pointer) -> Set<Address> {
    |                                                                  ------------ expected `vstd::set::Set<spec::AsyncDisk_t::Address>` because of return type
...

error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:137:9
    |
135 |       pub open spec fn tight_domain(self, index: LsnAUIndex, root: Pointer) -> Set<Address>
    |                                                                                ------------ expected `vstd::set::Set<spec::AsyncDisk_t::Address>` because of return type
136 |       {

error[E0599]: no method named `build_lsn_au_index_page_walk_consistency` found for struct `journal::LinkedJournal_v::DiskView` in the current scope
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:743:14
    |
743 |         self.build_lsn_au_index_page_walk_consistency(self.next(bottom));
    |              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1044:61
     |
1044 |             let sub_domain = dv.tight_domain(index.restrict(sub_lsns), sub_freshest_rec);
     |                                                    -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                                                    |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1047:98
     |
1047 |             &&& sub_dv.build_lsn_au_index_au_walk(sub_freshest_rec, sub_first) == index.restrict(sub_lsns)
     |                                                                                         -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                                                                                         |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1053:40
     |
1053 |         let sub_index = index.restrict(sub_lsns);
     |                               -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                               |
```

## splinter/AllocationJournal


compiler_diagnostics:
```text
error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:64:14
   |
64 |     Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn, |lsn| lsn_au_index[lsn])
   |     -------- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<nat>`, found `FnSpec<(nat,), bool>`
   |     |

error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:82:14
   |
82 |     Map::new(|lsn| start_lsn <= lsn < end_lsn, |lsn| value)
   |     -------- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<nat>`, found `FnSpec<(_,), bool>`
   |     |

error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:130:9
    |
126 | pub open spec(checked) fn au_addrs_past_pointer(ptr: Pointer) -> Set<Address> {
    |                                                                  ------------ expected `vstd::set::Set<spec::AsyncDisk_t::Address>` because of return type
...

error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:137:9
    |
135 |       pub open spec fn tight_domain(self, index: LsnAUIndex, root: Pointer) -> Set<Address>
    |                                                                                ------------ expected `vstd::set::Set<spec::AsyncDisk_t::Address>` because of return type
136 |       {

error[E0599]: no method named `build_lsn_au_index_page_walk_consistency` found for struct `journal::LinkedJournal_v::DiskView` in the current scope
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:743:14
    |
743 |         self.build_lsn_au_index_page_walk_consistency(self.next(bottom));
    |              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1044:61
     |
1044 |             let sub_domain = dv.tight_domain(index.restrict(sub_lsns), sub_freshest_rec);
     |                                                    -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                                                    |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1047:98
     |
1047 |             &&& sub_dv.build_lsn_au_index_au_walk(sub_freshest_rec, sub_first) == index.restrict(sub_lsns)
     |                                                                                         -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                                                                                         |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1053:40
     |
1053 |         let sub_index = index.restrict(sub_lsns);
     |                               -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                               |
```

## splinter/CoordinationSystem


tlc_diagnostics:
```text
TLC2 Version 2026.09.24.190251 (rev: 11305b4)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 126 and seed 4285626067001548032 with 1 worker on 32 cores with 1024MB heap and 64MB offheap memory [pid: 852295] (Linux 7.0.0-1012-aws amd64, Ubuntu 25.0.4.1 64bit, MSBDiskFPSet, DiskStateQueue).
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/CoordinationSystem/MC.tla
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/CoordinationSystem/State_tla.tla
Parsing file /tmp/tlc-5713747350588294421/_TLCTrace.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-5713747350588294421/Integers.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-5713747350588294421/Sequences.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-5713747350588294421/FiniteSets.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-5713747350588294421/TLC.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-5713747350588294421/Naturals.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-5713747350588294421/TLCExt.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module State_tla
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module MC
Linting of module State_tla
Linting of module TLCExt
Linting of module _TLCTrace
Linting of module MC
Starting... (2026-10-07 23:55:20)
Error: The constant parameter Dom_Key is not assigned a value by the configuration file.
Finished in 00s at (2026-10-07 23:55:20)
```

## splinter/CrashTolerantJournal


TLC: exploring_timeout, original 30-second budget.

## splinter/CrashTolerantMap


tlc_diagnostics:
```text
TLC2 Version 2026.09.24.190251 (rev: 11305b4)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 9 and seed 3926633267660486259 with 1 worker on 32 cores with 1024MB heap and 64MB offheap memory [pid: 855109] (Linux 7.0.0-1012-aws amd64, Ubuntu 25.0.4.1 64bit, MSBDiskFPSet, DiskStateQueue).
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/CrashTolerantMap/MC.tla
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/CrashTolerantMap/State_tla.tla
Parsing file /tmp/tlc-13508621151917412287/_TLCTrace.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-13508621151917412287/Integers.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-13508621151917412287/Sequences.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-13508621151917412287/FiniteSets.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-13508621151917412287/TLC.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-13508621151917412287/Naturals.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-13508621151917412287/TLCExt.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module State_tla
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module MC
Linting of module State_tla
Linting of module TLCExt
Linting of module _TLCTrace
Linting of module MC
Starting... (2026-10-07 23:55:53)
Error: The constant parameter Dom_Key is not assigned a value by the configuration file.
Finished in 00s at (2026-10-07 23:55:53)
```

## splinter/FilteredBetree


compiler_diagnostics:
```text
error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/FilteredBetree_v.rs:428:38
    |
428 |         OffsetMap{ offsets: Map::new(|k| true,
    |                             -------- ^^^^^^^^ expected `Set<Key>`, found `FnSpec<(_,), bool>`
    |                             |

error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/OffsetMap_v.rs:34:9
   |
30 |     pub open spec(checked) fn active_keys(self, offset: nat) -> Set<Key>
   |                                                                 -------- expected `vstd::set::Set<spec::KeyType_t::Key>` because of return type
...

error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/OffsetMap_v.rs:40:38
   |
40 |         OffsetMap{ offsets: Map::new(|k| self.offsets.contains_key(k), 
   |                             -------- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<Key>`, found `FnSpec<(Key,), bool>`
   |                             |

error: aborting due to 3 previous errors

For more information about this error, try `rustc --explain E0308`.
```

## splinter/LikesBetree


compiler_diagnostics:
```text
error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:234:22
    |
234 |     pub entries: Map<Address, BetreeNode>,
    |                      ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:303:89
    |
303 |     pub open spec(checked) fn node_children_respects_rank(self, ranking: Ranking, addr: Address) -> bool
    |                                                                                         ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:322:57
    |
322 |     pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool 
    |                                                         ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:327:55
    |
327 |     pub open spec(checked) fn modify_disk(self, addr: Address, node: BetreeNode) -> DiskView
    |                                                       ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:356:31
    |
356 |     spec fn repr(self) -> Set<Address>;
    |                               ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:361:16
    |
361 |     pub addr1: Address,
    |                ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:362:16
    |
362 |     pub addr2: Address,
    |                ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:371:45
    |
371 |     open spec(checked) fn repr(self) -> Set<Address>
    |                                             ^^^^^^^ ambiguous name
    |
```

## splinter/LikesJournal


compiler_diagnostics:
```text
error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesJournal_v.rs:34:9
   |
33 |     Map::new(
   |     -------- arguments to this function are incorrect
34 |         |k| lsn_addr_index.contains_key(k) && bdy <= k,

error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesJournal_v.rs:50:14
   |
50 |     Map::new(|x: LSN| start <= x < end, |x:LSN| value)
   |     -------- ^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<nat>`, found `FnSpec<(nat,), bool>`
   |     |

error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesJournal_v.rs:686:56
    |
686 |         let frozen_index = pre.lsn_addr_index.restrict(frozen_lsns);
    |                                               -------- ^^^^^^^^^^^ expected `Set<nat>`, found `Option<Set<nat>>`
    |                                               |

error[E0599]: no associated function or constant named `inv_next` found for struct `journal::LinkedJournal_v::LinkedJournal::State` in the current scope
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/LikesJournal_v.rs:799:48
    |
799 |           LinkedJournal_v::LinkedJournal::State::inv_next(pre.journal, post.journal, State::lbl_i(lbl), istep);
    |                                                  ^^^^^^^^ associated function or constant not found in `journal::LinkedJournal_v::LinkedJournal::State`
    |

error originates in the macro `state_machine` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: use of deprecated method `vstd::set::Set::<A>::finite`: Every Set is always finite, so this is always true.
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/disk/GenericDisk_v.rs:123:20
    |
123 |     requires addrs.finite()

error: aborting due to 4 previous errors; 3 warnings emitted

Some errors have detailed explanations: E0308, E0599.
For more information about an error, try `rustc --explain E0308`.
```

## splinter/LinkedBetreeVars


compiler_diagnostics:
```text
error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:234:22
    |
234 |     pub entries: Map<Address, BetreeNode>,
    |                      ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:303:89
    |
303 |     pub open spec(checked) fn node_children_respects_rank(self, ranking: Ranking, addr: Address) -> bool
    |                                                                                         ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:322:57
    |
322 |     pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool 
    |                                                         ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:327:55
    |
327 |     pub open spec(checked) fn modify_disk(self, addr: Address, node: BetreeNode) -> DiskView
    |                                                       ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:356:31
    |
356 |     spec fn repr(self) -> Set<Address>;
    |                               ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:361:16
    |
361 |     pub addr1: Address,
    |                ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:362:16
    |
362 |     pub addr2: Address,
    |                ^^^^^^^ ambiguous name
    |

error[E0659]: `Address` is ambiguous
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/betree/LinkedBetree_v.rs:371:45
    |
371 |     open spec(checked) fn repr(self) -> Set<Address>
    |                                             ^^^^^^^ ambiguous name
    |
```

## splinter/LinkedJournal


tlc_diagnostics:
```text
TLC2 Version 2026.09.24.190251 (rev: 11305b4)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 92 and seed -1531367684211897319 with 1 worker on 32 cores with 1024MB heap and 64MB offheap memory [pid: 855457] (Linux 7.0.0-1012-aws amd64, Ubuntu 25.0.4.1 64bit, MSBDiskFPSet, DiskStateQueue).
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/LinkedJournal/MC.tla
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/LinkedJournal/State_tla.tla
Parsing file /tmp/tlc-5089501617696868482/_TLCTrace.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-5089501617696868482/Integers.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-5089501617696868482/Sequences.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-5089501617696868482/FiniteSets.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-5089501617696868482/TLC.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-5089501617696868482/Naturals.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-5089501617696868482/TLCExt.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module State_tla
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module MC
Linting of module State_tla
Linting of module TLCExt
Linting of module _TLCTrace
Linting of module MC
Starting... (2026-10-07 23:55:57)
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2026-10-07 23:55:57.
Error: Invariant inv is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ unmarshalled_tail = [msgs |-> <<>>, seq_start |-> 0, seq_end |-> 0]
/\ truncated_journal = [disk_view |-> [entries |-> <<>>, boundary_lsn |-> 0], freshest_rec |-> [tag |-> "None"]]

State 2: <Next line 389, col 9 to line 389, col 30 of module State_tla>
/\ unmarshalled_tail = [msgs |-> (0 :> [key |-> [v0 |-> 0], message |-> [tag |-> "Define", value |-> [v0 |-> 0]]]), seq_start |-> 0, seq_end |-> 1]
/\ truncated_journal = [disk_view |-> [entries |-> <<>>, boundary_lsn |-> 0], freshest_rec |-> [tag |-> "None"]]

State 3: <Next line 389, col 9 to line 389, col 30 of module State_tla>
/\ unmarshalled_tail = [msgs |-> <<>>, seq_start |-> 1, seq_end |-> 1]
/\ truncated_journal = [disk_view |-> [entries |-> ([au |-> 0, page |-> 0] :> [message_seq |-> [msgs |-> (0 :> [key |-> [v0 |-> 0], message |-> [tag |-> "Define", value |-> [v0 |-> 0]]]), seq_start |-> 0, seq_end |-> 1], prior_rec |-> [tag |-> "None"]]), boundary_lsn |-> 0], freshest_rec |-> [v0 |-> [au |-> 0, page |-> 0], tag |-> "Some"]]

9 states generated, 4 distinct states found, 1 states left on queue.
The depth of the complete state graph search is 3.
Finished in 00s at (2026-10-07 23:55:57)
Trace exploration spec path: ./MC_TTrace_1791417356.tla
```

## splinter/PagedBetree


sany_diagnostics:
```text
Semantic errors:

*** Errors: 1

line 376, col 298 to line 376, col 315 of module State_tla

Unknown operator: `Defined_substitute'.
```

tlc_diagnostics:
```text
TLC2 Version 2026.09.24.190251 (rev: 11305b4)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 115 and seed 4550397429540369293 with 1 worker on 32 cores with 1024MB heap and 64MB offheap memory [pid: 855532] (Linux 7.0.0-1012-aws amd64, Ubuntu 25.0.4.1 64bit, MSBDiskFPSet, DiskStateQueue).
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/PagedBetree/MC.tla
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/PagedBetree/State_tla.tla
Parsing file /tmp/tlc-14286724918877907591/_TLCTrace.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-14286724918877907591/Integers.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-14286724918877907591/Sequences.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-14286724918877907591/FiniteSets.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-14286724918877907591/TLC.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-14286724918877907591/Naturals.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-14286724918877907591/TLCExt.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module State_tla
Semantic errors:

*** Errors: 1

line 376, col 298 to line 376, col 315 of module State_tla

Unknown operator: `Defined_substitute'.


Semantic processing of module TLCExt
Semantic errors:

*** Errors: 1

line 376, col 298 to line 376, col 315 of module State_tla

Unknown operator: `Defined_substitute'.


Semantic processing of module _TLCTrace
Semantic errors:

*** Errors: 1

line 376, col 298 to line 376, col 315 of module State_tla

Unknown operator: `Defined_substitute'.


Semantic processing of module MC
Semantic errors:

*** Errors: 1

line 376, col 298 to line 376, col 315 of module State_tla

Unknown operator: `Defined_substitute'.


Starting... (2026-10-07 23:55:57)
Error: Parsing or semantic analysis failed.
Finished in 00s at (2026-10-07 23:55:57)
```

## splinter/PivotBetree


sany_diagnostics:
```text
Semantic errors:

*** Errors: 1

line 623, col 539 to line 623, col 556 of module State_tla

Unknown operator: `Defined_substitute'.
```

tlc_diagnostics:
```text
TLC2 Version 2026.09.24.190251 (rev: 11305b4)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 98 and seed -3205914605275781863 with 1 worker on 32 cores with 1024MB heap and 64MB offheap memory [pid: 855856] (Linux 7.0.0-1012-aws amd64, Ubuntu 25.0.4.1 64bit, MSBDiskFPSet, DiskStateQueue).
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/PivotBetree/MC.tla
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/splinter/PivotBetree/State_tla.tla
Parsing file /tmp/tlc-16339575829672014726/_TLCTrace.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-16339575829672014726/Integers.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-16339575829672014726/Sequences.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-16339575829672014726/FiniteSets.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-16339575829672014726/TLC.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-16339575829672014726/Naturals.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-16339575829672014726/TLCExt.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module State_tla
Semantic errors:

*** Errors: 1

line 623, col 539 to line 623, col 556 of module State_tla

Unknown operator: `Defined_substitute'.


Semantic processing of module TLCExt
Semantic errors:

*** Errors: 1

line 623, col 539 to line 623, col 556 of module State_tla

Unknown operator: `Defined_substitute'.


Semantic processing of module _TLCTrace
Semantic errors:

*** Errors: 1

line 623, col 539 to line 623, col 556 of module State_tla

Unknown operator: `Defined_substitute'.


Semantic processing of module MC
Semantic errors:

*** Errors: 1

line 623, col 539 to line 623, col 556 of module State_tla

Unknown operator: `Defined_substitute'.


Starting... (2026-10-07 23:56:00)
Error: Parsing or semantic analysis failed.
Finished in 00s at (2026-10-07 23:56:00)
```

## splinter/UnifiedCrashAwareJournal


compiler_diagnostics:
```text
error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:64:14
   |
64 |     Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn, |lsn| lsn_au_index[lsn])
   |     -------- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<nat>`, found `FnSpec<(nat,), bool>`
   |     |

error[E0308]: mismatched types
  --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:82:14
   |
82 |     Map::new(|lsn| start_lsn <= lsn < end_lsn, |lsn| value)
   |     -------- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Set<nat>`, found `FnSpec<(_,), bool>`
   |     |

error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:130:9
    |
126 | pub open spec(checked) fn au_addrs_past_pointer(ptr: Pointer) -> Set<Address> {
    |                                                                  ------------ expected `vstd::set::Set<spec::AsyncDisk_t::Address>` because of return type
...

error[E0308]: mismatched types
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:137:9
    |
135 |       pub open spec fn tight_domain(self, index: LsnAUIndex, root: Pointer) -> Set<Address>
    |                                                                                ------------ expected `vstd::set::Set<spec::AsyncDisk_t::Address>` because of return type
136 |       {

error[E0599]: no method named `build_lsn_au_index_page_walk_consistency` found for struct `journal::LinkedJournal_v::DiskView` in the current scope
   --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:743:14
    |
743 |         self.build_lsn_au_index_page_walk_consistency(self.next(bottom));
    |              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1044:61
     |
1044 |             let sub_domain = dv.tight_domain(index.restrict(sub_lsns), sub_freshest_rec);
     |                                                    -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                                                    |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1047:98
     |
1047 |             &&& sub_dv.build_lsn_au_index_au_walk(sub_freshest_rec, sub_first) == index.restrict(sub_lsns)
     |                                                                                         -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                                                                                         |

error[E0308]: mismatched types
    --> /data/home/kirancodes/Documents/code/verus-research/campaign-real/sources/splinter/allocation_layer/AllocationJournal_v.rs:1053:40
     |
1053 |         let sub_index = index.restrict(sub_lsns);
     |                               -------- ^^^^^^^^ expected `Set<nat>`, found `Option<Set<_>>`
     |                               |
```

## nr/UnboundedLog-mono


tlc_diagnostics:
```text
TLC2 Version 2026.09.24.190251 (rev: 11305b4)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 130 and seed -6602626228516700938 with 1 worker on 32 cores with 1024MB heap and 64MB offheap memory [pid: 856360] (Linux 7.0.0-1012-aws amd64, Ubuntu 25.0.4.1 64bit, MSBDiskFPSet, DiskStateQueue).
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/nr/UnboundedLog-mono/MC.tla
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/nr/UnboundedLog-mono/State_tla.tla
Parsing file /tmp/tlc-18254954230112778345/_TLCTrace.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-18254954230112778345/Integers.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-18254954230112778345/Sequences.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-18254954230112778345/FiniteSets.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-18254954230112778345/TLC.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-18254954230112778345/Naturals.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-18254954230112778345/TLCExt.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module State_tla
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module MC
Linting of module State_tla
Linting of module TLCExt
Linting of module _TLCTrace
Linting of module MC
Starting... (2026-10-07 23:56:04)
Error: The constant parameter Table_arbitrary__tla_closed2 is not assigned a value by the configuration file.
Finished in 00s at (2026-10-07 23:56:04)
```

## nr/CyclicBuffer

- 1× **uninterpreted function carrier type PointsTo_Option_ConcreteLogEntry_DT cannot be constrained**, `vstd/cell.rs:132:5: 132:63 (#0)` (in `vstd::cell::impl&%2::mem_contents__tla_closed`).
- 1× **uninterpreted function carrier type CellId cannot be constrained**, `vstd/cell.rs:129:5: 129:45 (#0)` (in `vstd::cell::impl&%2::id__tla_closed`).
- 1× **uninterpreted function carrier type SyncSendIfSyncSend_tuple0 cannot be constrained**, `vstd/tokens.rs:88:10: 88:31 (#0)` (in `vstd::tokens::KeyValueToken::key__tla_closed`).
- 1× **uninterpreted function carrier type SyncSendIfSyncSend_tuple0 cannot be constrained**, `vstd/tokens.rs:87:10: 87:46 (#0)` (in `vstd::tokens::KeyValueToken::instance_id__tla_closed`).
- 1× **uninterpreted function carrier type SyncSendIfSyncSend_tuple0 cannot be constrained**, `/Users/kirancodes/Documents/code/verus-research/survey/repos/verus-lang_verified-node-replication/verified-node-replication/src/spec/unbounded_log.rs:265:1: 1171:2 (#355)` (in `nrspec::spec::unbounded_log::UnboundedLog::impl&%28::id__tla_closed`).
- 1× **uninterpreted function carrier type SyncSendIfSyncSend_tuple0 cannot be constrained**, `vstd/tokens.rs:89:10: 89:35 (#0)` (in `vstd::tokens::KeyValueToken::value__tla_closed`).

## nr/FlatCombiner


tlc_diagnostics:
```text
TLC2 Version 2026.09.24.190251 (rev: 11305b4)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 41 and seed -1632687198296098293 with 1 worker on 32 cores with 1024MB heap and 64MB offheap memory [pid: 858230] (Linux 7.0.0-1012-aws amd64, Ubuntu 25.0.4.1 64bit, MSBDiskFPSet, DiskStateQueue).
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/nr/FlatCombiner/MC.tla
Parsing file /data/home/kirancodes/Documents/code/verus-research/wt-export-closures/audit/export-closures/cumulative-scope-final/nr/FlatCombiner/State_tla.tla
Parsing file /tmp/tlc-1363793114163423554/_TLCTrace.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-1363793114163423554/Integers.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-1363793114163423554/Sequences.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-1363793114163423554/FiniteSets.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-1363793114163423554/TLC.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-1363793114163423554/Naturals.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-1363793114163423554/TLCExt.tla (jar:file:/data/home/kirancodes/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module State_tla
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module MC
Linting of module State_tla
Linting of module TLCExt
Linting of module _TLCTrace
Linting of module MC
Starting... (2026-10-07 23:56:09)
Error: The constant parameter Table_arbitrary__tla_closed is not assigned a value by the configuration file.
Finished in 00s at (2026-10-07 23:56:09)
```

