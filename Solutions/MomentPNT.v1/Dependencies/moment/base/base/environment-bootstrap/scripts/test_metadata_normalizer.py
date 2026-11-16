#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,time,tempfile
E=Path(__file__).resolve().parents[2];sys.path.insert(0,str(E));from replay_kernel_v1 import need,sha,load,publish
CODE=E/'environment-bootstrap/scripts/normalize_cache_metadata.py';ENV=E/'work/environment-cold-v1/ENVIRONMENT.json';OUT=E/'work/metadata-normalizer-controls-v1'
def main():
 need(not OUT.exists(),'fresh controls required');OUT.mkdir();started=time.monotonic();code_sha=sha(CODE);env=load(ENV);traces=load(E/'work/metadata-preflight-v1/PREPARED.json')['changes'];original={r['target']:sha(r['target'])for r in traces};records=[]
 for mode in range(3):
  flags=['-B']+(['-O']if mode==1 else['-OO']if mode==2 else[]);dest=OUT/('prepare-opt%d'%mode);scope=OUT/('prepare-scope-opt%d'%mode);cmd=[sys.executable,str(E.parent/'scripts/resource_scope.py'),'--family','root_generic','--memory-gib','8','--cpus','4','--wall','180','--out',str(scope),'--',sys.executable]+flags+[str(CODE),'--environment',str(ENV),'--out',str(dest)];child=subprocess.run(cmd,capture_output=True);(OUT/('prepare-opt%d.stdout'%mode)).write_bytes(child.stdout);(OUT/('prepare-opt%d.stderr'%mode)).write_bytes(child.stderr);need(child.returncode==0,'metadata full preflight failed');j=load(dest/'PREPARED.json');need(j['files_checked']==133055 and j['nontrace_payloads_exact']==133044 and j['apply_requested']is False and not(dest/'RECEIPT.json').exists(),'preflight semantics failed');records.append(dict(mode=mode,case='full133055-byte-preparation',command=cmd,exit_code=child.returncode,prepared_sha256=sha(dest/'PREPARED.json')))
  neg=OUT/('negative-opt%d'%mode);neg.mkdir()
  def reject(name,envpath,code=CODE,out=None):
   out=out or neg/(name+'-out');cmd=[sys.executable]+flags+[str(code),'--environment',str(envpath),'--out',str(out)];c=subprocess.run(cmd,capture_output=True);(neg/(name+'.stdout')).write_bytes(c.stdout);(neg/(name+'.stderr')).write_bytes(c.stderr);need(c.returncode!=0 and not(out/'PREPARED.json').exists()and not(out/'RECEIPT.json').exists(),'invalid normalizer input accepted');records.append(dict(mode=mode,case=name,command=cmd,exit_code=c.returncode,expected_rejection=True))
  stale=neg/'stale';stale.mkdir();(stale/'sentinel').write_text('keep');reject('stale-output',ENV,out=stale);need((stale/'sentinel').read_text()=='keep','stale output overwritten')
  for label,key,value in [('outside-owned-root','work',str(E.parent)),('wrong-bootstrap','bootstrap_script_sha256','0'*64),('wrong-compiler-version','compiler_version','wrong')]:
   j=dict(env);j[key]=value;p=neg/(label+'.json');p.write_text(json.dumps(j));reject(label,p)
  p=neg/'duplicate.json';p.write_text('{"work":1,"work":2}');reject('duplicate-json',p)
  p=neg/'nonfinite.json';p.write_text('{"n":1e999}');reject('nonfinite-json',p)
  for label,bad in [('bad-reference','environment-bootstrap/reference/APPROVED_PATH_DEPENDENT_TRACES.json.gz'),('bad-pin','environment/ENVIRONMENT_CONTENTS_RC2_V2.json')]:
   package=neg/label
   for rel in ['environment-bootstrap/scripts/normalize_cache_metadata.py','environment-bootstrap/reference/APPROVED_PATH_DEPENDENT_TRACES.json.gz','environment/ENVIRONMENT_CONTENTS_RC2_V2.json']:
    q=package/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((E/rel).read_bytes())
   q=package/bad;q.write_bytes(q.read_bytes()+b'\n');reject(label,ENV,code=package/'environment-bootstrap/scripts/normalize_cache_metadata.py')
  need(all(sha(p)==h for p,h in original.items()),'preparation or negative control changed actual fresh metadata')
 need(sha(CODE)==code_sha,'normalizer source changed during controls');publish(OUT/'RECEIPT.json',dict(status='METADATA_NORMALIZER_PREPARE_AND_REJECT_CLIS_PASS_0_O_OO',source_sha256=code_sha,test_source_sha256=sha(__file__),positive=3,negative=24,actual_full133055_file_hash_preflight_per_mode=True,no_actual_bootstrap_metadata_replaced=True,seconds=time.monotonic()-started,records=records))
 print('ALL3_FULL_METADATA_PREFLIGHTS_AND24_NEGATIVES_PASS')
if __name__=='__main__':main()
