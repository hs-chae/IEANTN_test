#!/usr/bin/env python3
"""Execute actual replay acceptance CLIs under normal, -O, and -OO."""
from pathlib import Path
import argparse,json,shutil,subprocess,sys,hashlib,time
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();o=a.out.resolve()
if o.exists():raise ValueError('fresh control directory required')
o.mkdir(parents=True);m=json.loads((B/'SOURCE_MANIFEST.json').read_text());rows=[];started=time.monotonic()
def packet(name):
 q=o/name;q.mkdir();shutil.copytree(B/'source',q/'source')
 for x in ['reproduce.py','SOURCE_MANIFEST.json','THEOREM_CENSUS.json','BUILD_CONTEXT.json']:shutil.copyfile(B/x,q/x)
 return q
def run(name,q,flags,opt,args,success):
 cmd=[sys.executable,*flags,str(q/'reproduce.py'),'--check','--optimize',opt,*args];r=subprocess.run(cmd,text=True,capture_output=True);(o/(name+'.stdout')).write_text(r.stdout);(o/(name+'.stderr')).write_text(r.stderr);ok=(r.returncode==0)==success
 row={'id':name,'command':cmd,'returncode':r.returncode,'expected_success':success,'matched':ok};rows.append(row)
 if not ok:raise ValueError('acceptance control failed:'+name)
for label,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
 run(label+'-valid',B,flags,label,[],True)
 for idx,row in enumerate(m['modules']):
  name=f'{label}-changed-child-{idx:02d}';q=packet(name);f=q/row['path'];f.write_bytes(f.read_bytes()+b'\n');run(name,q,flags,label,[],False)
 name=label+'-missing-child';q=packet(name);z=json.loads((q/'SOURCE_MANIFEST.json').read_text());z['modules'].pop();(q/'SOURCE_MANIFEST.json').write_text(json.dumps(z));run(name,q,flags,label,[],False)
 name=label+'-duplicate-key';q=packet(name);f=q/'SOURCE_MANIFEST.json';text=f.read_text();f.write_text('{"schema":"DUPLICATE",'+text[1:]);run(name,q,flags,label,[],False)
 name=label+'-wrong-mode';run(name,B,flags,'OO'if label!='OO'else'normal',[],False)
 name=label+'-unknown-option';run(name,B,flags,label,['--unchecked'],False)
receipt={'schema':'MOBIUS_COMPONENT_ACTUAL_CLI_CONTROLS_V1','status':'PASS_ALL36_ACTUAL_CLI_CONTROLS','count':len(rows),'all_routes':7,'modes':['normal','O','OO'],'validator_sha256':hashlib.sha256((B/'reproduce.py').read_bytes()).hexdigest(),'source_manifest_sha256':hashlib.sha256((B/'SOURCE_MANIFEST.json').read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-started,'controls':rows}
if len(rows)!=36:raise ValueError('control census mismatch')
tmp=o/'RESULT.json.tmp';tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(o/'RESULT.json');print(receipt['status'],len(rows))
