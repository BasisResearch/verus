"""Commit compact evidence and a reviewable table from cumulative.py's raw logs."""
import argparse
import collections
import hashlib
import json
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--tests', type=int, required=True)
ap.add_argument('--fixture-parent', default='regression-before')
ap.add_argument('--after-phase', default='after')
ap.add_argument('--parent-phase', default='parent')
ap.add_argument('--previous-phase')
ap.add_argument('--round2-parent-phase')
ap.add_argument('--round2-after-phase')
args = ap.parse_args()
HERE = Path(__file__).resolve().parent
phase_dirs = {'before':'before', 'parent':args.parent_phase, 'after':args.after_phase}
phases = {p: json.loads((HERE/f'cumulative-{d}/summary.json').read_text()) for p,d in phase_dirs.items()}
for phase, summary in phases.items():
    for row in summary['rows']:
        directory = HERE/f'cumulative-{phase_dirs[phase]}'/row['machine']
        sany = directory/'sany.log'
        if sany.exists() and not row.get('sany_ok'):
            log = sany.read_text()
            row['sany_diagnostics'] = log[log.find('Semantic errors:'):] if 'Semantic errors:' in log else log[-3500:]
        if row.get('tlc_errors'):
            row['tlc_diagnostics'] = (directory/'MC.log').read_text()[-6500:]

def counts(rows):
    return dict(targets=len(rows), exported=sum(r['export_status']=='exported' for r in rows),
        zero_refusals=sum(r['refusals']==0 for r in rows),
        zero_refusals_and_sany=sum(r['refusals']==0 and r.get('sany_ok',False) for r in rows),
        saved_bounds=sum(r['campaign_bounds'] for r in rows),
        completes=sum(r['completes'] for r in rows), explores=sum(r['explores'] for r in rows),
        refusals=sum(r['refusals'] or 0 for r in rows))
summary_counts={phase:{group:counts([r for r in s['rows'] if r['primary']==primary])
    for group,primary in [('primary',True),('supplemental',False)]} for phase,s in phases.items()}
old=HERE/args.fixture_parent;new=HERE/'regression-stacked'
golden={str(p.relative_to(old)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
    identical=p.read_bytes()==(new/p.relative_to(old)).read_bytes()) for p in old.rglob('*') if p.suffix in ['.tla','.cfg','.json']}
assert len(golden)==35 and all(x['identical'] for x in golden.values())
evidence=dict(fixture_parent=args.fixture_parent, base_commit=phases['after']['base_commit'],tests=args.tests,counts=summary_counts,phases=phases,golden=golden)
round2 = {}
if args.round2_parent_phase and args.round2_after_phase:
    for key, phase in [('parent',args.round2_parent_phase),('after',args.round2_after_phase)]:
        summary = json.loads((HERE/f'cumulative-{phase}/summary.json').read_text())
        for row in summary['rows']:
            if row.get('tlc_errors'):
                row['tlc_diagnostics'] = (HERE/f'cumulative-{phase}'/row['machine']/'MC.log').read_text()[-6500:]
        round2[key] = summary
    round2['before_option_fix'] = json.loads((HERE.parent/'export-partial/anvil-measurements.json').read_text())['before']
    evidence['round2_anvil'] = round2

previous_stack = None
if args.previous_phase:
    previous_stack = json.loads((HERE/f'cumulative-{args.previous_phase}/summary.json').read_text())
    evidence['previous_stack'] = dict(base_commit=previous_stack['base_commit'],
        head_commit=previous_stack['head_commit'],
        primary=counts([r for r in previous_stack['rows'] if r['primary']]))
previous = json.loads((HERE/'cumulative-after/summary.json').read_text())
evidence['scope_repair'] = dict(
    before_fix_commit='5412e3a2',
    before=next(r for r in previous['rows'] if r['machine']=='anvil/sub_api_sm'),
    after=next(r for r in phases['after']['rows'] if r['machine']=='anvil/sub_api_sm'),
    regression_tests=['tla_export_closure_record_definedness_keeps_bound_parameters',
        'tla_export_symbolic_record_does_not_hoist_unused_field_guards'])
(HERE/'cumulative-results.json').write_text(json.dumps(evidence,indent=2)+'\n')

lanes={
 'anvil/Cluster-adapter':'L1 trait tables; L4 reduces reachable records, exposing deeper callbacks/choices; still refused',
 'anvil/sub_api':'L1 trait tables; L3 carriers/guards; L4 action/choice reduction exposes deeper callbacks; still refused',
 'anvil/sub_api_sm':'L4 reduces helper receivers; choice over closure records remains',
 'anvil/sub_controller':'L1 trait tables + L4 record/receiver reduction jointly remove all refusals',
 'anvil/sub_network':'L4 removes both closure refusals',
 'ironkv/host_protocol_t':'L1 trait tables + L3 total collections already remove all refusals; L4 unchanged',
 'nrkernel/hlspec':'L1 trait table + L2 bit/Init + L3 carriers + L4 final bounded choose',
 'nrkernel/mmu_rl1':'L1/L2 trait/bit rules; L3 cached definedness removes expansion-limit refusals',
 'nrkernel/mmu_rl2':'L1/L2 trait/bit rules; L3 cached definedness removes export timeout',
 'nrkernel/mmu_rl3':'L1/L2 trait/bit rules; L3 cached definedness removes export timeout',
 'nrkernel/os':'L1/L2 trait/bit rules; L3 removes timeout; L4 removes choose; integer type bounds remain (os.rs:242,249; mmu/defs.rs:434)',
 'nrkernel/os_ext':'L2 bit/Init removes final refusal',
 'nr/AsynchronousSingleton':'L1 concrete dispatch/typed tables',
 'nr/SimpleLog':'L1 concrete dispatch/typed tables',
 'nr/UnboundedLog':'L1 concrete dispatch/typed tables; L3 carriers',
 'anvil/sub_vrs_reconcile':'L1 dispatch/tables removes refusals; L3 fixes Option projection through helper match arms (round-2 replay below)',
 'nr/UnboundedLog-mono':'L1 table + L3 guarded reads; unchanged config lacks table assignment',
 'nr/CyclicBuffer':'L1 dispatch/tables; see remaining located refusals',
 'nr/FlatCombiner':'L1 replaces uninterpreted refusal with table; original config lacks Table_arbitrary__tla_closed',
 'nr/RwLockSpec':'Existing bounded completion',
}
for r in phases['after']['rows']:
    name=r['machine']
    if name.startswith('splinter/'):
        if r['export_status']!='exported': note='Campaign Rust input does not compile; no lane unblocks it'
        elif name.split('/')[1] in ['PagedBetree','PivotBetree']: note=('Existing bounded completion; L3 dependency declarations repaired' if r['tlc_status']=='complete' else 'L3: see remaining SANY/TLC blocker')
        elif name.endswith('PagedJournal'): note='Existing bounded completion preserved'
        elif name.endswith('CoordinationSystem'): note='L3 guards/carriers; unchanged config lacks Dom_Key'
        elif name.endswith('CrashTolerantMap'): note='L3 guards/carriers; unchanged config lacks Dom_Key'
        else: note='L3 guarded partial reads/casts unblock evaluation; L4 unchanged'
        lanes[name]=note

def refusal(r):
    return str(r['refusals']) if r['refusals'] is not None else ('timeout' if r['export_status']=='timeout' else 'compile error')
def sany(r):
    return 'pass' if r.get('sany_ok') else ('fail' if r['export_status']=='exported' else 'not exported')
def tlc(r):
    status=r['tlc_status']
    label={'no_saved_bounds':'no saved bounds','complete':'complete','evaluation_error':'evaluation/config error','sany_error':'SANY error','timeout_before_progress':'timeout before progress','exploring_timeout':'progress; timeout','blocked_by_export':'export blocked','invariant_counterexample':'invariant CTI','complete_with_counterexample':'complete search with invariant CTI'}[status]
    if status == 'exploring_timeout': label+=f" (at least {r.get('distinct','?')} states reported)"
    elif status in ['complete','invariant_counterexample','complete_with_counterexample']: label+=f" ({r.get('distinct','?')} states)"
    return label
maps={p:{r['machine']:r for r in s['rows']} for p,s in phases.items()}
base = phases['after']['base_commit'][:8]
lines=[f'## Cumulative campaign after merge of `{base}`','',
 f'The table measures all 33 requested export targets: Anvil’s five (including both API adapters), IronKV host, nrkernel’s six, NR’s three, and all 18 Splinter attempts. Five additional campaign adapters/controls follow separately. A compiler error or timeout is **not** a zero-refusal export. `Before` uses the original campaign binary; `L1–3` uses the clean lane-3 checkout at `{base}`; `After` uses the merged lane-4 binary. Binary hashes and version strings are saved in `cumulative-results.json` (the parent binary embeds its pre-commit dirty version string).','']
for phase,s in summary_counts.items():
    p=s['primary'];lines.append(f"- **{phase}:** {p['zero_refusals']}/33 zero-refusal exports; {p['zero_refusals_and_sany']}/33 also pass SANY; {p['completes']}/9 saved-bound TLC runs complete; {p['explores']}/9 explore without an evaluation error.")
if previous_stack:
    old_counts = evidence['previous_stack']['primary']
    new_counts = summary_counts['after']['primary']
    lines += ['', f"Since the previous stack on `{previous_stack['base_commit'][:8]}`, zero-refusal exports **{old_counts['zero_refusals']}→{new_counts['zero_refusals']}**, zero-refusal exports passing SANY **{old_counts['zero_refusals_and_sany']}→{new_counts['zero_refusals_and_sany']}**, completed campaign-bound TLC runs **{old_counts['completes']}→{new_counts['completes']}**, and explorations **{old_counts['explores']}→{new_counts['explores']}**."]
lines+=['','The table distinguishes completed runs, invariant counterexamples, and progress until timeout. Lane 4’s additional zero-refusal targets over lane 3 are identified by the intermediate column.\n\nOriginal `MC.tla`, `MC.cfg`, and TLC commands/timeouts were replayed unchanged, with their hashes recorded. The original campaign has no saved bounds for the other 24 primary targets (round-2 Anvil replays are reported separately); no new constants, table interpretations, adapters, or bounds were invented. Reaching states before a TLC evaluation error does not count as exploration. Lane-3 restrictions and finite carriers remain explicitly reported approximations, so a completed bounded run is not a proof of the unrestricted source.','',
 'L1 = traits; L2 = nrkernel bit operations/partial Init; L3 = partial reads/finite carriers; L4 = closure reduction/bounded choose. Intermediate attribution also uses the committed lane reports (`artifacts/nrkernel/report.txt`, `audit/export-partial/REPORT.md`) and the trait lane’s recorded campaign results. More refusals can mean reduction reached previously hidden unsupported expressions.','']
for primary,title in [(True,'Requested campaign targets'),(False,'Additional campaign adapters and controls')]:
    lines+=['', '### '+title,'','| Target | Before | L1–3 | After | SANY parent → after | TLC before → after (original campaign bounds) | Lane contribution |','|---|---:|---:|---:|---|---|---|']
    for a in phases['after']['rows']:
        if a['primary']!=primary:continue
        name=a['machine'];b=maps['before'][name];p=maps['parent'][name]
        lines.append(f"| {name} | {refusal(b)} | {refusal(p)} | {refusal(a)} | {sany(p)} → {sany(a)} | {tlc(b)} → {tlc(a)} | {lanes[name]} |")
if round2:
    lines += ['', '### Round-2 Anvil harnesses', '',
        'These are additional bounded replays, separate from the original campaign counts above. Both use byte-identical saved `MC.tla`/`MC.cfg` files. Reproduce with `python3 audit/export-closures/cumulative.py round2-replay --round2 --verus source/target-verus/release/verus`. No TLC command was saved for these harnesses, so the replay uses lane 3’s 30-second cap, one worker, and `-continue`. A completed search with a counterexample is not a clean invariant pass.', '',
        '| Machine | L1–3 refusals | L1–4 refusals | Parent TLC | Merged stack TLC |',
        '|---|---:|---:|---|---|']
    parents = {r['machine']:r for r in round2['parent']['rows']}
    for row in round2['after']['rows']:
        parent = parents[row['machine']]
        lines.append(f"| {row['machine']} | {refusal(parent)} | {refusal(row)} | {tlc(parent)} | {tlc(row)} |")
    lines += ['',
        'Network: lane 4 removes both closure refusals and the unchanged transport harness completes with nine distinct states. Controller: the original-campaign export above confirms lane 4 removes all nine parent closure refusals; SANY passes. Its round-2 controller harness was marked preliminary/unvalidated by that campaign, so no bounded controller verdict is claimed.', '',
        'VRS: the preceding fb8014b0 stack completed a seven-state search (with the saved harness’s expected not_error counterexample). The incoming ca16f117 parent and this merge both emit distinct specialized table names such as Table_marshal_spec_2, while the unchanged saved MC.cfg assigns the older Table_marshal_spec__tla_closed names. TLC therefore stops before exploration with an unassigned-constant error. This is an inherited harness/configuration mismatch; the table does not claim the previous seven-state result for this merge. Exact diagnostics and the unchanged bound hashes are retained in the evidence.']
lines+=['','### Validation and remaining blockers','',
 f'**{args.tests} exporter tests passed**, with `TLA2TOOLS_JAR` set. All **35** example/Raft `.tla`/`.cfg`/`.json` artifacts are byte-identical against the incoming parent. Workspace formatting and clippy, including the exporter test target, pass with warnings denied. The merge preserves the lower lanes’ tests, trace-arm bookkeeping, centralized specialization, and both restriction and choice reporting; captured environments in partial-read analysis now use the same immutable `Arc<Env>` representation as closure reduction.','',
 'Every remaining refusal, including its exact source location and multiplicity, is listed in [BLOCKERS.md](BLOCKERS.md). That file also records compiler, SANY, TLC configuration/evaluation, and timeout failures. The machine-readable report retains each individual refusal. The lane-4 `sub_api_sm` SANY regression is fixed: definedness analysis follows consumed symbolic fields and keeps their guards under the reduction’s LET bindings. It no longer emits guards for unused record fields. Both a bound-parameter closure record and the former unbound `kind` reproducer are TLC-checked. Independent lower-lane limitations and repairs are reflected in the parent and cumulative columns; their exact remaining diagnostics are in the blocker report.','',
 'Exporter suite: `export PATH=$HOME/.cargo/bin:$PATH; export TMPDIR=$HOME/tmp; source tools/activate; cd source; TLA2TOOLS_JAR=$HOME/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar timeout 1800 vargo test --release --vstd-no-verify -p rust_verify_test --test tla_export -- --test-threads=4`. Fixture comparison uses the existing `toydb-pr-30/src/raft/safety.rs` because `base/toydb/src/raft/safety.rs` is absent.\n\nReproduce with `python3 audit/export-closures/cumulative.py before --original-deps --verus ../base/verus/source/target-verus/release/verus`, then `parent` with the lane-3 binary and `after` with `source/target-verus/release/verus`; run `summarize-cumulative.py --tests <passed-count> --fixture-parent regression-parent-ca16 --parent-phase parent-ca16 --after-phase merged-ca16-final --round2-parent-phase round2-parent-ca16 --round2-after-phase round2-merged-ca16-final` after `regression.py regression-stacked source/target-verus/release/verus`. Raw commands/logs and modules are retained in ignored `cumulative-*` directories. Historical lane-4-only measurements in `results.json` are superseded by `cumulative-results.json`.']
report=(HERE/'REPORT.md').read_text().split('## Cumulative campaign')[0].split('## Reproduction')[0]+'\n'+'\n'.join(lines)+'\n'
(HERE/'REPORT.md').write_text(report)
block=['# Remaining cumulative campaign blockers','', 'Locations below are emitted by the exporter or compiler; repeated refusals are counted rather than hidden. Timeouts have no completed refusal report and therefore no inferred source-level cause.','']
for a in phases['after']['rows']:
    if not (a.get('refusal_details') or a['export_status']!='exported' or not a.get('sany_ok') or a['tlc_status'] not in ['no_saved_bounds','complete']):continue
    block+=['## '+a['machine'],'']
    counts=collections.Counter((d['what'],d['location'],d.get('in_function','')) for d in a.get('refusal_details',[]))
    for (what,loc,fun),n in counts.items():block.append(f'- {n}× **{what}**, `{loc}` (in `{fun}`).')
    for key in ['compiler_diagnostics','sany_diagnostics','tlc_diagnostics']:
        if a.get(key):
            txt=a[key] if isinstance(a[key],str) else '\n'.join(a[key])
            block+=['',key+':','```text',txt.rstrip(),'```']
    if a['export_status']=='timeout':block+=['','Export exceeded the original 90-second timeout. No completed report; construct/location unknown.']
    if a['tlc_status'] in ['timeout_before_progress','exploring_timeout']:block+=['',f"TLC: {a['tlc_status']}, original {a['tlc_budget_seconds']}-second budget."]
    block+=['']
if round2:
    for a in round2['after']['rows']:
        if not a.get('tlc_diagnostics'): continue
        block += ['## Round-2 '+a['machine'], '', 'Unchanged campaign harness:', '',
            '```text', a['tlc_diagnostics'].rstrip(), '```', '']
(HERE/'BLOCKERS.md').write_text('\n'.join(block)+'\n')
# Use repository URLs in the external PR description.
url='https://github.com/BasisResearch/verus/blob/kg/export-closures/audit/export-closures/'
body=report.replace('[BLOCKERS.md](BLOCKERS.md)',f'[BLOCKERS.md]({url}BLOCKERS.md)')
body+=f'\n[Full machine-readable evidence]({url}cumulative-results.json) · [Merge validation and hashes]({url}merge-validation.json)\n'
(HERE/'pr-body.log').write_text(body)
print(json.dumps(summary_counts,indent=2))
