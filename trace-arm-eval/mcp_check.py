import json, subprocess, os, pathlib, re, time
root=pathlib.Path(__file__).resolve().parents[1]; out=root/'trace-arm-eval'; base=root.parent/'base'
env=dict(os.environ,VERUS_BIN=str(root/'source/target-verus/release/verus'),VERUS_PROJECT_ROOT=str(root),JAVA_TOOL_OPTIONS='-Xss256m')
p=subprocess.Popen([str(base/'verus-tools-mcp/target/release/verus-tools-mcp')],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=(out/'mcp-stderr.log').open('w'),text=True,env=env)
seq=0
def rpc(method,params):
 global seq
 seq+=1;p.stdin.write(json.dumps(dict(jsonrpc='2.0',id=seq,method=method,params=params))+'\n');p.stdin.flush()
 while True:
  l=p.stdout.readline()
  if not l: raise RuntimeError('server closed')
  x=json.loads(l)
  if x.get('id')==seq: return x

def call(name,args): return rpc('tools/call',dict(name=name,arguments=args))
results=[]
try:
 rpc('initialize',dict(protocolVersion='2024-11-05',capabilities={},clientInfo=dict(name='trace-arm-check',version='1')))
 p.stdin.write(json.dumps(dict(jsonrpc='2.0',method='notifications/initialized'))+'\n');p.stdin.flush()
 for row in json.loads((out/'after-timings.json').read_text()):
  d=out/'after'/row['crate']; consts=(d/'State_tla_trace.cfg').read_text().split('\nCONSTANTS\n')[-1]
  (d/'session.cfg').write_text((d/'State_tla.cfg').read_text()+'\nCONSTANTS\n'+consts)
  opened=call('tlc_open',dict(spec=str(d/'State_tla.tla'),config=str(d/'session.cfg'),workers=1))
  text='\n'.join(c.get('text','') for c in opened.get('result',{}).get('content',[])); m=re.search(r'session ([0-9a-f-]{36})',text)
  if not m: raise RuntimeError(opened)
  t=time.monotonic(); checked=call('tlc_conform',dict(session_id=m[1],trace=str(root.parent/'wild'/row['log']),budget_ms=30000))
  record=dict(crate=row['crate'],seconds=round(time.monotonic()-t,3),result=checked)
  results.append(record);print(json.dumps(record),flush=True)
  call('tlc_close',dict(session_id=m[1]))
finally:
 p.terminate();p.wait(timeout=10)
 (out/'mcp-results.json').write_text(json.dumps(results,indent=2))
