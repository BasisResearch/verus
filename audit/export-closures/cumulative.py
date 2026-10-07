"""Replay the complete stacked-export campaign without altering its sources or bounds."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT.parent
CAMPAIGN = RESEARCH / 'campaign-real/results'
AUDIT = ROOT / 'audit/export-closures'
SPLINTER = ['AbstractJournal', 'AbstractMap', 'AllocationBetree', 'AllocationBranchBetree',
    'AllocationCrashAwareJournal', 'AllocationJournal', 'CoordinationSystem',
    'CrashTolerantJournal', 'CrashTolerantMap', 'FilteredBetree', 'LikesBetree',
    'LikesJournal', 'LinkedBetreeVars', 'LinkedJournal', 'PagedBetree', 'PagedJournal',
    'PivotBetree', 'UnifiedCrashAwareJournal']
PRIMARY = (['anvil/'+n for n in ['Cluster-adapter', 'sub_api', 'sub_api_sm', 'sub_controller', 'sub_network']]
    + ['ironkv/host_protocol_t']
    + ['nrkernel/'+n for n in ['hlspec', 'mmu_rl1', 'mmu_rl2', 'mmu_rl3', 'os', 'os_ext']]
    + ['nr/'+n for n in ['AsynchronousSingleton', 'SimpleLog', 'UnboundedLog']]
    + ['splinter/'+n for n in SPLINTER])
SUPPLEMENTAL = ['anvil/sub_vrs_reconcile', 'nr/UnboundedLog-mono', 'nr/CyclicBuffer',
    'nr/FlatCombiner', 'nr/RwLockSpec']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('phase')
    ap.add_argument('--verus', type=Path, required=True)
    ap.add_argument('--original-deps', action='store_true')
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--only', nargs='+')
    args = ap.parse_args()
    binary = args.verus.resolve()
    dest = AUDIT / ('cumulative-' + args.phase)
    dest.mkdir(exist_ok=True)
    env = dict(os.environ, PATH=str(Path.home()/'.cargo/bin')+':'+os.environ['PATH'],
        TMPDIR=str(Path.home()/'tmp'), VERUS_MCP_ENABLED='1')
    deps = dest / 'deps'
    if not args.original_deps:
        deps.mkdir(exist_ok=True)
        for name, src in [
            ('verus_temporal_logic', RESEARCH/'survey/repos/anvil-verifier_verus-tla/src/lib.rs'),
            ('k8s_openapi', RESEARCH/'survey/work/anvil/specroot/k8s_openapi_stub.rs')]:
            cmd = ['timeout', '90', str(binary), str(src), '--crate-type=lib', '--crate-name', name,
                '--no-verify', '--compile', '--export', str(deps/(name+'.vir')),
                '-o', str(deps/('lib'+name+'.rlib'))]
            proc = subprocess.run(cmd, env=env, cwd=ROOT, capture_output=True, text=True)
            (deps/(name+'.log')).write_text(proc.stdout+proc.stderr)
            if proc.returncode:
                raise RuntimeError('dependency build failed: '+name)

    def one(name):
        old = CAMPAIGN/name
        out = dest/name
        if out.exists():
            shutil.rmtree(out)  # Only this runner's evidence, inside this worktree.
        out.mkdir(parents=True)
        cmd = json.loads((old/'command.json').read_text())
        cmd[2] = str(binary)
        cmd[cmd.index('--log-dir')+1] = str(out/'export')
        cmd = [str(RESEARCH/'campaign-real'/a) if a.startswith('sources/') else a for a in cmd]
        if not args.original_deps:
            for i, arg in enumerate(cmd):
                if '=' in arg and arg.split('=')[0] in ['verus_temporal_logic','k8s_openapi']:
                    lib = arg.split('=')[0]
                    cmd[i] = lib+'='+str(deps/('lib'+lib+'.rlib' if arg.endswith('.rlib') else lib+'.vir'))
        (out/'command.json').write_text(json.dumps(cmd, indent=2)+'\n')
        start = time.monotonic()
        proc = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
        log = proc.stdout+proc.stderr
        (out/'export.log').write_text(log)
        row = dict(machine=name, primary=name in PRIMARY, export_rc=proc.returncode,
            export_seconds=round(time.monotonic()-start,2), refusals=None,
            export_status='timeout' if proc.returncode==124 else 'compiler_error',
            campaign_bounds=(old/'MC-command.json').exists(), tlc_status='no_saved_bounds',
            explores=False, completes=False)
        reports = sorted((out/'export').glob('*.tla.json'))
        if proc.returncode == 0 and reports:
            report = json.loads(reports[0].read_text())
            row.update(export_status='exported', refusals=len(report['refusals']),
                holes=len(report['holes']), restrictions=len(report.get('restrictions', [])),
                refusal_details=report['refusals'], choices=report.get('choices', []),
                init_unassigned=report.get('init_unassigned'),
                init_enumerated=report.get('init_enumerated'))
            spec = reports[0].with_suffix('')
            jar = Path.home()/'.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar'
            sany = subprocess.run(['timeout','30','java','-Xmx1g','-cp',str(jar),'tla2sany.SANY',spec.name],
                cwd=spec.parent, capture_output=True, text=True)
            text = sany.stdout+sany.stderr
            (out/'sany.log').write_text(text)
            row['sany_ok'] = sany.returncode==0 and ('Semantic processing of module '+spec.stem) in text and '*** Errors' not in text and 'Fatal errors' not in text
            if row['campaign_bounds']:
                shutil.copyfile(spec, out/spec.name)
                row['bound_files'] = {}
                for filename in ['MC.tla','MC.cfg']:
                    shutil.copyfile(old/filename,out/filename)
                    assert (old/filename).read_bytes()==(out/filename).read_bytes()
                    row['bound_files'][filename] = digest(out/filename)
                tlc = json.loads((old/'MC-command.json').read_text())
                (out/'MC-command.json').write_text(json.dumps(tlc,indent=2)+'\n')
                proc = subprocess.run(tlc,cwd=out,env=env,capture_output=True,text=True)
                text = proc.stdout+proc.stderr
                (out/'MC.log').write_text(text)
                row['tlc_rc'] = proc.returncode
                row['tlc_budget_seconds'] = tlc[1]
                counts = re.findall(r'([\d,]+) states generated[^\n]*?([\d,]+) distinct states found',text)
                if counts:
                    row.update(generated=int(counts[-1][0].replace(',','')),distinct=int(counts[-1][1].replace(',','')))
                row['tlc_errors'] = [line for line in text.splitlines() if line.startswith('Error:')][:8]
                violation = bool(re.search(r'Error: Invariant \S+ is violated',text))
                if 'Model checking completed.' in text and not row['tlc_errors']:
                    row.update(tlc_status='complete',explores=True,completes=True)
                elif violation and proc.returncode != 124:
                    row.update(tlc_status='invariant_counterexample',explores=True)
                elif proc.returncode == 124 and not row['tlc_errors']:
                    row['tlc_status'] = 'exploring_timeout' if counts else 'timeout_before_progress'
                    row['explores'] = bool(counts)
                else:
                    row['tlc_status'] = 'sany_error' if 'Parsing or semantic analysis failed' in text else 'evaluation_error'
        else:
            row['compiler_diagnostics'] = re.findall(r'(?:error[^\n]*\n(?:[^\n]*\n){0,5})',log)[:8]
            if row['campaign_bounds']:
                row['tlc_status'] = 'blocked_by_export'
        (out/'measurement.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({k:v for k,v in row.items() if k in ['machine','export_status','refusals','tlc_status','distinct']}),flush=True)
        return row

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(one,args.only or PRIMARY+SUPPLEMENTAL))
    provenance = dict(phase=args.phase,binary=str(binary),binary_version=(binary.parent/'version.txt').read_text(),
        sha256={p.name:digest(p) for p in [binary,binary.parent/'rust_verify']},
        base_commit=subprocess.check_output(['git','rev-parse','origin/kg/export-partial'],cwd=ROOT,text=True).strip(),
        head_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),rows=rows)
    (dest/'summary.json').write_text(json.dumps(provenance,indent=2)+'\n')

if __name__ == '__main__':
    main()
