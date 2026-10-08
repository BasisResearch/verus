"""Replay the saved campaign commands without modifying campaign sources or bounds."""
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
CAMPAIGN = ROOT.parent / 'campaign-real/results'
PARTIAL = ['nr/UnboundedLog-mono', 'splinter/AbstractJournal', 'splinter/AbstractMap',
           'splinter/CrashTolerantJournal', 'splinter/CrashTolerantMap', 'splinter/LinkedJournal']
COLLECTIONS = ['nr/UnboundedLog', 'ironkv/delegation_map_t', 'ironkv/host_protocol_t',
               'ironkv/host_impl_t', 'nrkernel/hlspec', 'nrkernel/mmu_rl1',
               'nrkernel/mmu_rl2', 'nrkernel/mmu_rl3', 'nrkernel/os']


REGRESSIONS = ['splinter/PagedBetree', 'splinter/PivotBetree', 'nrkernel/mmu_rl1', 'nrkernel/mmu_rl2', 'nrkernel/mmu_rl3', 'nrkernel/os']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('group', choices=['partial', 'collections', 'fixtures', 'regressions', 'anvil'])
    ap.add_argument('phase')
    ap.add_argument('--verus', type=Path, required=True)
    ap.add_argument('--export-seconds', type=int, default=90)
    ap.add_argument('--tlc-seconds', type=int, default=30)
    ap.add_argument('--jobs', type=int, default=1)
    args = ap.parse_args()
    binary = args.verus.resolve()
    dest = ROOT / 'audit/export-partial' / args.phase
    dest.mkdir(exist_ok=True)
    env = dict(os.environ, PATH=str(Path.home()/'.cargo/bin')+':'+os.environ['PATH'],
               TMPDIR=str(Path.home()/'tmp'), VERUS_MCP_ENABLED='1')
    campaign = ROOT.parent / 'campaign-real/round2' if args.group == 'anvil' else CAMPAIGN
    if args.group == 'anvil':
        deps = dest/'deps'
        deps.mkdir(exist_ok=True)
        for crate in ['verus_temporal_logic', 'k8s_openapi']:
            cmd = json.loads((campaign/'deps'/f'{crate}-command.json').read_text())
            cmd[2] = str(binary)
            for flag in ['--export', '-o']:
                i = cmd.index(flag)+1
                cmd[i] = str(deps/Path(cmd[i]).name)
            (deps/f'{crate}-command.json').write_text(json.dumps(cmd, indent=2)+'\n')
            result = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
            (deps/f'{crate}.log').write_text(result.stdout+result.stderr)
            if result.returncode:
                raise RuntimeError(f'{crate} dependency build failed; see {deps}')
    rows = []
    if args.group == 'fixtures':
        inputs = [(f.stem, f, f.stem + {'adder_sync':'::Adder', 'toggle_sync':'::Toggle',
                  'assert_sync':'::Guarded'}.get(f.stem, ''))
                  for f in sorted((ROOT/'examples/tla').glob('*.rs'))]
        # The documented base/toydb checkout lacks safety.rs on this box.
        inputs.append(('toydb', ROOT.parent/'trace-arm-eval/toydb/src/raft/safety.rs', 'safety'))
    else:
        inputs = [(name, None, None) for name in ({'partial': PARTIAL, 'collections': COLLECTIONS, 'regressions': REGRESSIONS, 'anvil': ['anvil/sub_network', 'anvil/sub_controller', 'anvil/sub_vrs_reconcile']}[args.group])]
    def run_one(item):
        name, source, module = item
        out = dest / name
        out.mkdir(parents=True, exist_ok=True)
        export = out / 'export'
        if export.exists():
            shutil.rmtree(export)
        if source:
            cmd = ['timeout', str(args.export_seconds), str(binary), '-V', 'tla-export='+module,
                   '--log-dir', str(export), '--no-verify', str(source), '--crate-type=lib']
        else:
            cmd = json.loads((campaign/name/'command.json').read_text())
            if isinstance(cmd, dict):
                a = cmd['arguments']
                cmd = ['timeout', str(args.export_seconds), str(binary), '-V', 'tla-export='+a['module'],
                       '--log-dir', str(export), a['path'], *a.get('extra_args', [])]
            cmd[1:3] = [str(args.export_seconds), str(binary)]
            cmd[cmd.index('--log-dir')+1] = str(export)
            cmd = [str(ROOT.parent/'campaign-real'/x) if x.startswith('sources/') else x for x in cmd]
        if args.group == 'anvil':
            cmd = [x.split('=')[0]+'='+str(deps/Path(x).name)
                   if '=' in x and '/round2/deps/' in x else x for x in cmd]
        (out/'command.json').write_text(json.dumps(cmd, indent=2)+'\n')
        started = time.monotonic()
        p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
        (out/'export.log').write_text(p.stdout+p.stderr)
        row = {'id':name, 'export_rc':p.returncode, 'export_seconds':round(time.monotonic()-started,3), 'status':'export_error'}
        reports = list(export.glob('*.tla.json'))
        if p.returncode == 0 and reports:
            report = json.loads(reports[0].read_text())
            row.update(status='exported', refusals=len(report['refusals']), holes=len(report['holes']),
                       restrictions=len(report.get('restrictions', [])),
                       reasons=sorted({r['what'] for r in report['refusals']}))
            spec = next(export.glob('*_tla.tla'))
            jar = Path.home()/'.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar'
            sany = ['timeout', '30', 'java', '-cp', str(jar), 'tla2sany.SANY', str(spec)]
            (out/'SANY-command.json').write_text(json.dumps(sany, indent=2)+'\n')
            check = subprocess.run(sany, cwd=ROOT, env=env, capture_output=True, text=True)
            result = check.stdout+check.stderr
            (out/'SANY.log').write_text(result)
            row['sany_status'] = 'ok' if (check.returncode == 0 and
                f'Semantic processing of module {spec.stem}' in result and
                not re.search(r'error', result, re.I)) else 'error'
            if row['sany_status'] == 'error':
                row['status'] = 'sany_error'
            if args.group != 'fixtures' and ((campaign/name/'MC-command.json').exists() or (args.group == 'anvil' and (campaign/name/'MC.cfg').exists())):
                spec = next(export.glob('*_tla.tla'))
                shutil.copyfile(spec, out/spec.name)
                for filename in ['MC.tla', 'MC.cfg']:
                    shutil.copyfile(campaign/name/filename, out/filename)
                command_file = campaign/name/'MC-command.json'
                tlc = json.loads(command_file.read_text()) if command_file.exists() else [
                    'timeout', str(args.tlc_seconds), 'java', '-Xmx1g', '-cp', str(jar),
                    'tlc2.TLC', '-deadlock', '-continue', '-workers', '1', 'MC.tla']
                tlc[1] = str(args.tlc_seconds)
                (out/'MC-command.json').write_text(json.dumps(tlc, indent=2)+'\n')
                p = subprocess.run(tlc, cwd=out, env=env, capture_output=True, text=True)
                text = p.stdout+p.stderr
                (out/'MC.log').write_text(text)
                row['tlc_rc'] = p.returncode
                row['invariant_violations'] = sorted(set(re.findall(r'Error: Invariant (\S+) is violated', text)))
                row['exploration_complete'] = 'Model checking completed.' in text
                counts = re.findall(r'(\d+) states generated[^\n]*?(\d+) distinct states found', text)
                if counts:
                    row.update(generated=int(counts[-1][0]), distinct=int(counts[-1][1]))
                if 'Model checking completed.' in text:
                    row['status'] = 'complete'
                elif re.search(r'Error: Invariant \S+ is violated', text):
                    row['status'] = 'invariant_violation'
                elif p.returncode == 124:
                    row['status'] = 'exploring_timeout' if counts else 'timeout_before_progress'
                elif 'Parsing or semantic analysis failed' in text:
                    row['status'] = 'sany_error'
                else:
                    row['status'] = 'tlc_error'
                row['errors'] = [line for line in text.splitlines() if line.startswith('Error:')][:5]
        return row

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for row in pool.map(run_one, inputs):
            rows.append(row)
            print(json.dumps(row), flush=True)
    provenance = {'binary':str(binary), 'group':args.group, 'phase':args.phase,
                  'export_seconds':args.export_seconds, 'tlc_seconds':args.tlc_seconds, 'jobs':args.jobs,
                  'sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in [binary, binary.parent/'rust_verify'] if p.exists()}, 'rows':rows}
    (dest/'summary.json').write_text(json.dumps(provenance, indent=2)+'\n')


if __name__ == '__main__':
    main()
