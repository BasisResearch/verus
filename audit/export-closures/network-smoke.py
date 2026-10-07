"""Supplemental bound: one valid message, multiplicity at most two; 30s timeout."""
import pathlib,subprocess,sys,json,shutil
base=pathlib.Path('audit/export-closures')/sys.argv[1]/'anvil/sub_network'
spec=base/'export/NetworkState_tla.tla';dest=base/'smoke';dest.mkdir(exist_ok=True)
shutil.copy(spec,dest/spec.name)
extra=r'''
Host == [tag |-> "APIServer"]
Content == [tag |-> "ExternalRequest", v0 |-> <<>>]
Message == [src |-> Host, dst |-> Host, rpc_id |-> 0, content |-> Content]
Empty == [x \in {} |-> x]
Send == {Empty, [x \in {Message} |-> 1]}
Hosts == {Host}
Contents == {Content}
Ids == {0}
Bound == \A m \in DOMAIN in_flight : in_flight[m] <= 2
'''
(dest/'MC.tla').write_text('---- MODULE MC ----\nEXTENDS NetworkState_tla\n'+extra+'\n====\n')
(dest/'MC.cfg').write_text('INIT Init\nNEXT Next\nCONSTRAINT Bound\nCONSTANT\n Dom_MessageOps_MessageOps_send <- Send\n Dom_Message_Message_src <- Hosts\n Dom_Message_Message_dst <- Hosts\n Dom_Message_Message_rpc_id <- Ids\n Dom_Message_Message_content <- Contents\n')
jar=pathlib.Path.home()/'.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar'
cmd=['timeout','30','java','-Xmx1g','-cp',str(jar),'tlc2.TLC','-deadlock','-continue','-workers','1','MC.tla']
p=subprocess.run(cmd,cwd=dest,capture_output=True,text=True);(dest/'tlc.log').write_text(p.stdout+p.stderr);(dest/'command.json').write_text(json.dumps(cmd));print(p.returncode,p.stdout[-1800:],p.stderr)
