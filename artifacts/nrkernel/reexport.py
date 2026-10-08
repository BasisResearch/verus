from pathlib import Path
import json, subprocess, os, sys
root=Path.cwd(); research=root.parent
phase=sys.argv[1]; binary=Path(sys.argv[2]).resolve()
env=dict(os.environ, PATH=str(Path.home()/'.cargo/bin')+':'+os.environ['PATH'], TMPDIR=str(Path.home()/'tmp'), VERUS_MCP_ENABLED='1')
out=root/'artifacts/nrkernel'/phase; out.mkdir(parents=True,exist_ok=True)
rows=[]
for name in ['hlspec','mmu_rl1','mmu_rl2','mmu_rl3','os','os_ext']:
 old=research/'campaign-real/results/nrkernel'/name
 cmd=json.loads((old/'command.json').read_text());cmd[2]=str(binary)
 dest=out/name;dest.mkdir(exist_ok=True);cmd[cmd.index('--log-dir')+1]=str(dest)
 (dest/'command.json').write_text(json.dumps(cmd,indent=2))
 p=subprocess.run(cmd,env=env,capture_output=True,text=True)
 (dest/'export.log').write_text(p.stdout+p.stderr)
 reports=list(dest.glob('*.tla.json')); row={'machine':name,'exit':p.returncode}
 if reports:
  j=json.loads(reports[0].read_text());row.update(refusals=len(j['refusals']),init_unassigned=j['init_unassigned'],init_enumerated=j['init_enumerated'],holes=len(j['holes']))
 rows.append(row);print(row,flush=True)
(out/'summary.json').write_text(json.dumps(rows,indent=2))
