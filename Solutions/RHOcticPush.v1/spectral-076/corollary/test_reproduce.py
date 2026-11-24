#!/usr/bin/env python3
"""Actual normal/-O/-OO readback controls; remove only owned copied fixtures."""
from pathlib import Path
import argparse,importlib.util,json,os,shutil,subprocess,sys,time
H=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('two_fifths_reader',H/'reproduce.py')
V=importlib.util.module_from_spec(spec);spec.loader.exec_module(V)
need,sha,read,save=V.need,V.sha,V.read,V.save

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 original=a.run.resolve();out=a.out.resolve();V.validate(original);need(not out.exists()and out.parent.is_dir(),'fresh owned tests namespace');out.mkdir();scratch=out/'owned-regenerable-fixtures';scratch.mkdir()
 cases=[('valid',None),('relocated',None),('source','source/object association'),('object','source/object association'),('foreign','foreign application object'),('omitted','omitted declared application import'),('native','nonstandard/native theorem axiom'),('duplicate','duplicate JSON key'),('float_counter','strict source census'),('overflow','nonfinite JSON number'),('bool_resource','strict resource admission')]
 rows=[];start=time.monotonic()
 for opt in ['', '-O','-OO']:
  for kind,gate in cases:
   label=(opt or 'normal').replace('-','')+'-'+kind;target=original if kind=='valid'else scratch/label
   if kind!='valid':shutil.copytree(original,target,symlinks=True)
   rr=read(target/'RESULT.json')
   if kind=='source':
    f=target/'source/BoxClassicalScalar.lean';f.write_bytes(f.read_bytes()+b'\n-- mutation\n')
   elif kind=='object':
    f=target/'objects/BoxClassicalScalar.olean';f.write_bytes(f.read_bytes()+b'mutation')
   elif kind in ['foreign','omitted']:
    q=rr['probes'][0];f=target/'BoxClassicalScalar.deps.stdout';lines=f.read_text().splitlines()
    if kind=='foreign':f.write_text('\n'.join(lines+['/tmp/unmapped/Other.olean'])+'\n')
    else:
     generic=[x for x in lines if '/lib/lean/Init.olean'in x];need(generic,'actual generic dependency');f.write_text(generic[0]+'\n')
    q['stdout_sha256']=sha(f)
   elif kind=='native':
    f=target/'BoxClassicalScalar.stdout';text=f.read_text();startax=text.index('depends on axioms: [')+len('depends on axioms: [');end=text.index(']',startax);f.write_text(text[:startax]+'Lean.ofReduceBool'+text[end:]);rr['build'][0]['stdout_sha256']=sha(f)
   elif kind=='float_counter':rr['fresh_scientific_sources']=2.0
   elif kind=='bool_resource':rr['resource_admission']['compiler_address_limit_bytes']=True
   if kind not in ['valid','relocated']:save(target/'RESULT.json',rr)
   if kind=='duplicate':
    f=target/'RESULT.json';f.write_text(f.read_text().replace('{','{"status":"duplicate",',1))
   elif kind=='overflow':
    f=target/'RESULT.json';text=f.read_text();key='"seconds":';i=text.index(key)+len(key);j=text.index(',',i);f.write_text(text[:i]+' 1e400'+text[j:])
   cmd=[sys.executable]+([opt]if opt else[])+[str(H/'reproduce.py'),'--verify',str(target)];t=time.monotonic();cp=subprocess.run(cmd,text=True,capture_output=True)
   so=out/(label+'.stdout');se=out/(label+'.stderr');so.write_text(cp.stdout);se.write_text(cp.stderr)
   need((cp.returncode==0)if gate is None else(cp.returncode!=0 and gate in cp.stderr),'actual expected CLI gate:'+label)
   if gate is None:need(cp.stdout.strip()=='PASS_BOX_TWO_FIFTHS_READBACK','actual positive output')
   rows.append({'case':label,'command':cmd,'returncode':cp.returncode,'seconds':time.monotonic()-t,'expected_gate':gate,'stdout_sha256':sha(so),'stderr_sha256':sha(se)})
   if kind!='valid':
    need(target.parent==scratch and target.resolve().is_relative_to(out)and not target.is_symlink(),'owned exact regenerable cleanup');shutil.rmtree(target)
   print(label,cp.returncode,flush=True)
 need(len(rows)==33 and not list(scratch.iterdir()),'all33actual decisions andcleanup')
 rr={'status':'PASS_ALL33_TWO_FIFTHS_ACTUAL_CLI_CONTROLS','reader_sha256':sha(H/'reproduce.py'),'test_sha256':sha(__file__),'accepted_result_sha256':sha(original/'RESULT.json'),'cases':rows,'seconds':time.monotonic()-start,'cleanup':'Only checked reproducible copiedfixtures removed; alloriginalsource/proof/result preserved.','relocation':'Byte-identical artifact relocation/readback, not another source compilation.'};save(out/'RESULT.json',rr);print(rr['status'])
if __name__=='__main__':main()
