import pathlib, sys, subprocess, json, time, importlib.util, re, os
ROOT=pathlib.Path(__file__).resolve().parents[1]; WILD=ROOT.parent/'wild'; OUT=ROOT/'trace-arm-eval'
JAR=pathlib.Path.home()/'.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar'
def load(crate, script):
 p=WILD/crate/script; sys.path.insert(0,str(p.parent)); sys.path.insert(0,str(WILD/'tools'))
 spec=importlib.util.spec_from_file_location(crate,p); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
cases=[('raft-rs','progress',next((WILD/'raft-rs/traces/fixed/harness').glob('*flow_control_move*/1504.ndjson'))),('lru-rs','lru',WILD/'lru-rs/traces/fixed/tests__test_pop_lru__0.ndjson'),('rust-circular-buffer','cbuf',WILD/'rust-circular-buffer/traces/fixed/rust_out/main-3884610/1.ndjson')]
version=sys.argv[1]; verus=pathlib.Path(sys.argv[2]).resolve(); limit=int(sys.argv[3]) if len(sys.argv)>3 else 120
results=[]
for crate,module,log in cases:
 d=OUT/version/crate; d.mkdir(parents=True,exist_ok=True)
 env=dict(os.environ,VERUS_MCP_ENABLED='1',TMPDIR=str(pathlib.Path.home()/'tmp'),PATH=str(pathlib.Path.home()/'.cargo/bin')+':'+os.environ['PATH'])
 subprocess.run(['timeout','120',str(verus),'-V',f'tla-export={module}','--log-dir',str(d),'--no-verify',str(WILD/crate/'model'/f'{module}.rs')],env=env,check=True,stdout=subprocess.DEVNULL,stderr=(d/'export.log').open('w'))
 if crate=='raft-rs': consts,n=load(crate,'tools/conform.py').domains(log)
 elif crate=='rust-circular-buffer': consts,n,big=load(crate,'conform.py').constants_for(log); assert not big
 else:
  m=load(crate,'conform.py'); mk,caps,n=m.scan(log); size=1 << (mk+1).bit_length(); keys='{'+','.join(map(str,range(size)))+'}'; capset='{'+','.join(map(str,sorted(caps|{1,2,3})))+'}';consts=[f'Dom_{h} = {keys}' for h in m.KEY_HOLES]+[f'Dom_{h} = {capset}' for h in m.CAP_HOLES]
 cfg=(d/'State_tla_trace.cfg'); cfg.write_text(cfg.read_text().replace('"trace.ndjson"',json.dumps(str(log)))+'\nCONSTANTS\n'+'\n'.join(consts)+'\n')
 t=time.monotonic()
 with (d/'tlc.log').open('w') as f:
  p=subprocess.run(['timeout',str(limit),'java','-Xss256m','-Xmx4g','-XX:+UseParallelGC','-cp',str(JAR),'tlc2.TLC','-workers','1','-deadlock','-config',str(cfg),'State_tla_trace.tla'],cwd=d,stdout=f,stderr=subprocess.STDOUT)
 text=(d/'tlc.log').read_text(); depth=re.search(r'depth of the complete state graph search is (\d+)',text)
 r=dict(crate=crate,steps=n,seconds=round(time.monotonic()-t,3),exit=p.returncode,depth=int(depth[1]) if depth else None,log=str(log.relative_to(WILD)),limit=limit)
 results.append(r); print(json.dumps(r),flush=True); (OUT/f'{version}-timings.json').write_text(json.dumps(results,indent=2))
