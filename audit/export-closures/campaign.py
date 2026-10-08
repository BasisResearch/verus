import json, pathlib, subprocess, os, sys
root=pathlib.Path.home()/'Documents/code/verus-research'
work=pathlib.Path.cwd(); out=work/'audit/export-closures'/sys.argv[1]; out.mkdir(parents=True,exist_ok=True)
verus=sys.argv[2]
env=dict(os.environ,PATH=str(pathlib.Path.home()/'.cargo/bin')+':'+os.environ['PATH'],TMPDIR=str(pathlib.Path.home()/'tmp'),VERUS_MCP_ENABLED='1')
rows=[]
for machine in (sys.argv[3:] or ['anvil/Cluster-adapter','anvil/sub_api','anvil/sub_api_sm','anvil/sub_controller','anvil/sub_network','ironkv/host_protocol_t']):
 old=root/'campaign-real/results'/machine
 r=json.loads((old/'result.json').read_text()); d=out/machine; d.mkdir(parents=True,exist_ok=True)
 if sys.argv[1] != 'before':
  r['args']=[(a.split('=')[0]+'='+str(work/'audit/export-closures/deps'/('lib'+a.split('=')[0]+'.rlib' if a.endswith('.rlib') else a.split('=')[0]+'.vir'))) if '=' in a and a.split('=')[0] in ['verus_temporal_logic','k8s_openapi'] else a for a in r['args']]
 cmd=['timeout','90',verus,'-V','tla-export='+r['module'],'--log-dir',str(d/'export'),'--no-verify',r['source'],*(r['args'] or [])]
 p=subprocess.run(cmd,env=env,capture_output=True,text=True)
 (d/'export.log').write_text(p.stdout+p.stderr);(d/'command.json').write_text(json.dumps(cmd,indent=2))
 row=dict(machine=machine,rc=p.returncode,refusals=None,holes=None)
 for f in (d/'export').glob('*.tla.json'):
  j=json.loads(f.read_text()); row.update(refusals=len(j['refusals']),holes=len(j['holes']),choices=len(j.get('choices',[])))
 rows.append(row);print(row,flush=True)
(out/'summary.json').write_text(json.dumps(rows,indent=2))
