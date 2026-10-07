from pathlib import Path
import subprocess,json,sys,re
root=Path.cwd(); base=root/'artifacts/nrkernel'; jar=Path.home()/'.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar'
phase=sys.argv[1]; rows=[]
for name in ['hlspec','mmu_rl1','mmu_rl2','mmu_rl3','os','os_ext']:
 d=base/phase/name; spec=d/'State_tla.tla'
 p=subprocess.run(['timeout','60','java','-Xmx1g','-cp',str(jar),'tla2sany.SANY',str(spec)],capture_output=True,text=True,cwd=root)
 (d/'sany.log').write_text(p.stdout+p.stderr)
 row={'machine':name,'sany_ok':p.returncode==0 and '*** Errors' not in p.stdout and 'Fatal errors' not in p.stdout}
 if name=='os_ext':
  j=json.loads((d/'State_tla.tla.json').read_text())
  vals={'Const_c_core_count':'1','Const_c_node_count':'1','Const_c_phys_mem_size':'8192','Const_c_range_mem':'<<0, 1>>','Const_c_range_ptmem':'<<4096, 8192>>','Dom_MemRegion_MemRegion_base':'{4096}','Dom_MemRegion_MemRegion_size':'{4096}','Dom_ShootdownVector_ShootdownVector_open_requests':'{{}}','Dom_ISet_MemRegion':'{{}}'}
  defs=[];cfg='INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nCONSTRAINT Bound\n'
  for c in sorted({h['constant'] for h in j['holes']}):
   defs.append('Value_'+c+' == '+vals.get(c,'{0}'));cfg+='CONSTANT '+c+' <- Value_'+c+'\n'
  (d/'MC.tla').write_text('---- MODULE MC ----\nEXTENDS State_tla\n'+'\n'.join(defs)+'\nBound == Cardinality(allocated) <= 1\n====\n')
  (d/'MC.cfg').write_text(cfg)
  cmd=['timeout','30','java','-Xmx1g','-cp',str(jar),'tlc2.TLC','-deadlock','-continue','-workers','1','-metadir',str(d/'states'),'-config',str(d/'MC.cfg'),str(d/'MC.tla')]
  (d/'tlc-command.json').write_text(json.dumps(cmd,indent=2));p=subprocess.run(cmd,capture_output=True,text=True,cwd=root);out=p.stdout+p.stderr
  (d/'tlc.log').write_text(out);row.update(tlc_exit=p.returncode,tlc_finished='Model checking completed' in out,tlc_distinct=re.findall(r'(\d+) distinct states found',out),tlc_error=[l for l in out.splitlines() if l.startswith('Error:')][:2])
 rows.append(row);print(row,flush=True)
(base/phase/'checks.json').write_text(json.dumps(rows,indent=2))
