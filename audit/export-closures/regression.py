import pathlib, subprocess, os, sys, json
root=pathlib.Path.home()/'Documents/code/verus-research'; work=pathlib.Path.cwd()
verus=sys.argv[2]; out=work/'audit/export-closures'/sys.argv[1]; out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,PATH=str(pathlib.Path.home()/'.cargo/bin')+':'+os.environ['PATH'],TMPDIR=str(pathlib.Path.home()/'tmp'),VERUS_MCP_ENABLED='1')
fixtures=[(work/'examples/tla'/f,mod) for f,mod in [('counter.rs','test_crate'),('adder_sync.rs','test_crate::Adder'),('toggle_sync.rs','test_crate::Toggle'),('assert_sync.rs','test_crate::Guarded'),('mutex_tla.rs','test_crate'),('mutex_liveness.rs','test_crate')]]
fixtures.append((root/'toydb-pr-30/src/raft/safety.rs','test_crate'))
for src,mod in fixtures:
 d=out/src.stem;d.mkdir(parents=True,exist_ok=True)
 cmd=['timeout','90',verus,'-V','tla-export='+mod,'--log-dir',str(d),'--no-verify','--crate-name=test_crate','--crate-type=lib',str(src)]
 p=subprocess.run(cmd,env=env,capture_output=True,text=True);(d/'export.log').write_text(p.stdout+p.stderr)
 print(src.name,p.returncode,flush=True)
