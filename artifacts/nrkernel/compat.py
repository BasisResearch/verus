from pathlib import Path
import subprocess,os,sys,json,hashlib
root=Path.cwd();phase=sys.argv[1];binary=Path(sys.argv[2]).resolve();env=dict(os.environ, PATH=str(Path.home()/'.cargo/bin')+':'+os.environ['PATH'], TMPDIR=str(Path.home()/'tmp'), VERUS_MCP_ENABLED='1')
toydb=root/'artifacts/nrkernel/toydb/safety.rs'
if not toydb.exists():
 toydb.parent.mkdir(parents=True,exist_ok=True)
 toydb.write_bytes(subprocess.check_output(['git','-C',str(root.parent/'base/toydb'),'show','c23eebe8c678bda4693748f8a5cbe05ddba2b2ff:src/raft/safety.rs']))
fixtures=list((root/'examples/tla').glob('*.rs'))+[root/'artifacts/nrkernel/toydb/safety.rs']
for src in fixtures:
 dest=root/'artifacts/nrkernel'/('compat-'+phase)/src.stem;dest.mkdir(parents=True,exist_ok=True)
 p=subprocess.run(['timeout','60',str(binary),'-V','tla-export='+src.stem+{'adder_sync':'::Adder','toggle_sync':'::Toggle','assert_sync':'::Guarded'}.get(src.stem,'')+(':inv_wf,inv_hosts,inv_msgs,inv_lterms,inv_ack_persist,inv_vote_persist,inv_commits,inv_leader_completeness,inv_commit_msgs,inv_host_commits,inv_commit_leaders,inv_reads' if src.stem=='safety' else ''),'--no-verify','--log-dir',str(dest),str(src),'--crate-type=lib'],env=env,capture_output=True,text=True)
 (dest/'export.log').write_text(p.stdout+p.stderr);print(src.name,p.returncode,flush=True)
