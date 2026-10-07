from pathlib import Path
import subprocess,os
root=Path.home()/'Documents/code/verus-research';d=Path('audit/export-closures/deps').resolve();d.mkdir(exist_ok=True)
v=Path('source/target-verus/release/verus').resolve()
env=dict(os.environ,VERUS_MCP_ENABLED='1',PATH=str(Path.home()/'.cargo/bin')+':'+os.environ['PATH'],TMPDIR=str(Path.home()/'tmp'))
for name,src in [('verus_temporal_logic',root/'survey/repos/anvil-verifier_verus-tla/src/lib.rs'),('k8s_openapi',root/'survey/work/anvil/specroot/k8s_openapi_stub.rs')]:
 cmd=['timeout','90',str(v),str(src),'--crate-type=lib','--crate-name',name,'--no-verify','--compile','--export',str(d/(name+'.vir')),'-o',str(d/('lib'+name+'.rlib'))]
 r=subprocess.run(cmd,env=env,capture_output=True,text=True);(d/(name+'.log')).write_text(r.stdout+r.stderr);print(name,r.returncode,(r.stdout+r.stderr)[-600:])
