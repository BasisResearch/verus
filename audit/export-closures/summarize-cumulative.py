"""Commit compact evidence and a reviewable table from cumulative.py's raw logs."""
import argparse
import collections
import hashlib
import json
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--tests', type=int, required=True)
ap.add_argument('--after-phase', default='after')
ap.add_argument('--parent-phase', default='parent')
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
old=HERE/'regression-before';new=HERE/'regression-stacked'
golden={str(p.relative_to(old)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
    identical=p.read_bytes()==(new/p.relative_to(old)).read_bytes()) for p in old.rglob('*') if p.suffix in ['.tla','.cfg']}
assert len(golden)==28 and all(x['identical'] for x in golden.values())
evidence=dict(base_commit=phases['after']['base_commit'],tests=args.tests,counts=summary_counts,phases=phases,golden=golden)
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
 'nrkernel/mmu_rl1':'L1/L2 remove trait/bit refusals; L3 definedness expansion limit remains',
 'nrkernel/mmu_rl2':'L1/L2 remove trait/bit refusals; L3/L4 export times out',
 'nrkernel/mmu_rl3':'L1/L2 remove trait/bit refusals; L3/L4 export times out',
 'nrkernel/os':'L1/L2 remove trait/bit refusals; L3/L4 export times out',
 'nrkernel/os_ext':'L2 bit/Init removes final refusal',
 'nr/AsynchronousSingleton':'L1 concrete dispatch/typed tables',
 'nr/SimpleLog':'L1 concrete dispatch/typed tables',
 'nr/UnboundedLog':'L1 concrete dispatch/typed tables; L3 carriers',
 'anvil/sub_vrs_reconcile':'L1 dispatch/tables removes refusals; L4 unchanged',
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
    label={'no_saved_bounds':'no saved bounds','complete':'complete','evaluation_error':'evaluation/config error','sany_error':'SANY error','timeout_before_progress':'timeout before progress','exploring_timeout':'progress; timeout','blocked_by_export':'export blocked','invariant_counterexample':'invariant CTI'}[status]
    if status in ['complete','exploring_timeout','invariant_counterexample']: label+=f" ({r.get('distinct','?')} states)"
    return label
maps={p:{r['machine']:r for r in s['rows']} for p,s in phases.items()}
base = phases['after']['base_commit'][:8]
lines=[f'## Cumulative campaign after rebase onto `{base}`','',
 f'The table measures all 33 requested export targets: Anvil’s five (including both API adapters), IronKV host, nrkernel’s six, NR’s three, and all 18 Splinter attempts. Five additional campaign adapters/controls follow separately. A compiler error or timeout is **not** a zero-refusal export. `Before` uses the original campaign binary; `L1–3` uses the clean lane-3 checkout at `{base}`; `After` uses the rebased lane-4 binary. Binary hashes and version strings are saved in `cumulative-results.json` (the parent binary embeds its pre-commit dirty version string).','']
for phase,s in summary_counts.items():
    p=s['primary'];lines.append(f"- **{phase}:** {p['zero_refusals']}/33 zero-refusal exports; {p['zero_refusals_and_sany']}/33 also pass SANY; {p['completes']}/9 saved-bound TLC runs complete; {p['explores']}/9 explore without an evaluation error.")
lines+=['','The table distinguishes completed runs, invariant counterexamples, and progress until timeout. Lane 4’s additional zero-refusal targets over lane 3 are identified by the intermediate column.\n\nOriginal `MC.tla`, `MC.cfg`, and TLC commands/timeouts were replayed unchanged, with their hashes recorded. The other 24 primary targets have no saved campaign bounds; no new constants, table interpretations, adapters, or bounds were invented. Reaching states before a TLC evaluation error does not count as exploration. Lane-3 restrictions and finite carriers remain explicitly reported approximations, so a completed bounded run is not a proof of the unrestricted source.','',
 'L1 = traits; L2 = nrkernel bit operations/partial Init; L3 = partial reads/finite carriers; L4 = closure reduction/bounded choose. Intermediate attribution also uses the committed lane reports (`artifacts/nrkernel/report.txt`, `audit/export-partial/REPORT.md`) and the trait lane’s recorded campaign results. More refusals can mean reduction reached previously hidden unsupported expressions.','']
for primary,title in [(True,'Requested campaign targets'),(False,'Additional campaign adapters and controls')]:
    lines+=['', '### '+title,'','| Target | Before | L1–3 | After | SANY parent → after | TLC before → after (campaign bounds) | Lane contribution |','|---|---:|---:|---:|---|---|---|']
    for a in phases['after']['rows']:
        if a['primary']!=primary:continue
        name=a['machine'];b=maps['before'][name];p=maps['parent'][name]
        lines.append(f"| {name} | {refusal(b)} | {refusal(p)} | {refusal(a)} | {sany(p)} → {sany(a)} | {tlc(b)} → {tlc(a)} | {lanes[name]} |")
lines+=['','### Validation and remaining blockers','',
 f'**{args.tests} exporter tests passed**, with `TLA2TOOLS_JAR` set. All **28** example/Raft `.tla`/`.cfg` artifacts are byte-identical. The rebase preserves the lower lanes’ tests and both restriction and choice reporting; captured environments in partial-read analysis now use the same immutable `Arc<Env>` representation as closure reduction.','',
 'Every remaining refusal, including its exact source location and multiplicity, is listed in [BLOCKERS.md](BLOCKERS.md). That file also records compiler, SANY, TLC configuration/evaluation, and timeout failures. The machine-readable report retains each individual refusal. The lane-4 `sub_api_sm` SANY regression is fixed: definedness analysis follows consumed symbolic fields and keeps their guards under the reduction’s LET bindings. It no longer emits guards for unused record fields. Both a bound-parameter closure record and the former unbound `kind` reproducer are TLC-checked. Independent lower-lane limitations and repairs are reflected in the parent and cumulative columns; their exact remaining diagnostics are in the blocker report.','',
 'Exporter suite: `export PATH=$HOME/.cargo/bin:$PATH; export TMPDIR=$HOME/tmp; source tools/activate; cd source; TLA2TOOLS_JAR=$HOME/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar timeout 1800 vargo test --release --vstd-no-verify -p rust_verify_test --test tla_export -- --test-threads=4`. Fixture comparison uses the existing `toydb-pr-30/src/raft/safety.rs` because `base/toydb/src/raft/safety.rs` is absent.\n\nReproduce with `python3 audit/export-closures/cumulative.py before --original-deps --verus ../base/verus/source/target-verus/release/verus`, then `parent` with the lane-3 binary and `after` with `source/target-verus/release/verus`; run `summarize-cumulative.py --tests <passed-count>` after `regression.py regression-stacked source/target-verus/release/verus`. Raw commands/logs and modules are retained in ignored `cumulative-*` directories. Historical lane-4-only measurements in `results.json` are superseded by `cumulative-results.json`.']
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
(HERE/'BLOCKERS.md').write_text('\n'.join(block)+'\n')
# Use repository URLs in the external PR description.
url='https://github.com/BasisResearch/verus/blob/kg/export-closures/audit/export-closures/'
body=report.replace('[BLOCKERS.md](BLOCKERS.md)',f'[BLOCKERS.md]({url}BLOCKERS.md)')
body+=f'\n[Full machine-readable evidence]({url}cumulative-results.json)\n'
(HERE/'pr-body.log').write_text(body)
print(json.dumps(summary_counts,indent=2))
