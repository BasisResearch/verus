"""Refresh evidence after the final exporter build, without changing campaign inputs."""
from pathlib import Path
import subprocess,sys,json,hashlib,collections
p=Path('audit/export-closures');v=str(Path('source/target-verus/release/verus').resolve())
def run(script,*args):
 subprocess.run([sys.executable,str(p/script),*args],check=True)
run('build-deps.py')
run('campaign.py','after',v)
run('campaign.py','nrkernel-after',v,'nrkernel/hlspec','nrkernel/os')
run('regression.py','regression-after',v)
run('network-smoke.py','after')
jar=Path.home()/'.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar'
sany={}
for phase in ['before','after']:
 for spec in sorted((p/phase).glob('*/*/export/*_tla.tla')):
  proc=subprocess.run(['timeout','20','java','-cp',str(jar),'tla2sany.SANY',spec.name],cwd=spec.parent,capture_output=True,text=True)
  log=proc.stdout+proc.stderr;(spec.parent/'sany.log').write_text(log)
  sany[str(spec.relative_to(p))]=proc.returncode==0 and 'Semantic processing of module '+spec.stem in log and '*** Errors' not in log and 'Fatal errors' not in log
before=json.loads((p/'before/summary.json').read_text());after=json.loads((p/'after/summary.json').read_text());rows=[]
for b,a in zip(before,after):
 j=json.loads(next((p/'after'/a['machine']/'export').glob('*.tla.json')).read_text())
 rows.append(dict(machine=a['machine'],before_refusals=b['refusals'],after_refusals=a['refusals'],after_holes=a['holes'],choices=j.get('choices',[]),remaining_by_kind=dict(collections.Counter(r['what'] for r in j['refusals'])),remaining_refusals=j['refusals']))
reg=[]
for f in sorted((p/'regression-before').glob('*/*')):
 if f.suffix in ['.tla','.cfg']:
  g=p/'regression-after'/f.relative_to(p/'regression-before');assert f.read_bytes()==g.read_bytes(),str(f)
  reg.append(dict(file=str(f.relative_to(p/'regression-before')),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),byte_identical=True))
network=(p/'after/anvil/sub_network/smoke/tlc.log').read_text()
assert 'Model checking completed. No error has been found.' in network
assert '11 states generated, 3 distinct states found' in network
r=dict(base_branch='kg/export-partial',base_commit=subprocess.check_output(['git','rev-parse','origin/kg/export-partial'],text=True).strip(),before_zero_refusal=sum(x['before_refusals']==0 for x in rows),after_zero_refusal=sum(x['after_refusals']==0 for x in rows),machine_count=6,campaign_tlc_bounds_available=False,supplemental_tlc=dict(machine='anvil/sub_network',before='refusal at first transition',after='completed',timeout_seconds=30,generated=11,distinct=3),machines=rows,regression=reg,sany=sany,nrkernel_before=json.loads((p/'nrkernel-before/summary.json').read_text()),nrkernel_after=json.loads((p/'nrkernel-after/summary.json').read_text()))
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print('SANY:',json.dumps(sany,indent=2));print('Byte-identical artifacts:',len(reg))
