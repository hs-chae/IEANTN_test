#!/usr/bin/env python3
"""Bounded actual-CLI controls for ordinary numerical acceptance, all Python modes."""
from pathlib import Path
import argparse,hashlib,json,os,struct,subprocess,sys,time
p=argparse.ArgumentParser();p.add_argument('--study',type=Path,required=True);p.add_argument('--scratch',type=Path,required=True);a=p.parse_args();r=a.study.resolve();d=a.scratch.resolve();s=Path(__file__).resolve().parents[1];o=r/'evidence/numerical-cli-controls-v2';o.mkdir(exist_ok=False);temp=d/'numerical-cli-controls-v2';temp.mkdir(exist_ok=False);results=[];i=0
for opt in [[],['-O'],['-OO']]:
 for mode in ['actual','unit']:
  for checker in ['check_exact_cells_v2.py','check_finite_independent_v2.py']:
   cases=['valid','duplicate_json','nonfinite_json','missing_chunk','bad_partition','wrong_mode','bad_primecount'] if 'independent' in checker else ['valid','duplicate_json','nonfinite_json','missing_chunk','bad_partition','wrong_mode','bad_rounding','bad_adjacency']
   for case in cases:
    label=f'{i:03d}';i+=1;study=o/label;name='finite-'+mode+'-pilot';e=study/'evidence'/name;e.mkdir(parents=True);scratch=temp/label/'ivy-ramanujan-source-pv-20261119';scratch.mkdir(parents=True);os.link(d/'generate_finite',scratch/'generate_finite');os.link(d/'independent_finite_check',scratch/'independent_finite_check');source_link=study/'network/Solutions';source_link.mkdir(parents=True);(source_link/s.name).symlink_to(s,target_is_directory=True);cd=scratch/name;cd.mkdir();raw=bytearray((d/('pilot-'+mode+'.bin')).read_bytes());nr=json.loads((r/'evidence/finite-pilot'/(mode+'.stdout')).read_text())
    if case=='bad_primecount':struct.pack_into('<Q',raw,24,0)
    if case=='bad_rounding':
     elo=1<<60;term=elo
     for k in range(1,21):term//=k;elo+=term
     struct.pack_into('<Q',raw,40,1);struct.pack_into('<Q',raw,48,38358837683*elo if 38358837683*elo<(1<<64) else (1<<64)-1)
    if case=='bad_adjacency':struct.pack_into('<Q',raw,56,struct.unpack_from('<Q',raw,56)[0]+1)
    (cd/'0.bin').write_bytes(raw);rec={'chunk':0,'begin':nr['begin'],'end_exclusive':nr['end_exclusive'],'exit_code':0,'certificate_bytes':len(raw),'certificate_sha256':hashlib.sha256(raw).hexdigest(),'numeric_result':nr}
    run={'status':'UNTRUSTED_NUMERICAL_GENERATION_COMPLETE','formal_verification':False,'mode':mode,'begin':nr['begin'],'end_inclusive':nr['end_exclusive']-1,'chunks':1,'workers':1,'records':[rec],'certificate_bytes':len(raw),'source_sha256':hashlib.sha256((s/'c/generate_finite.cpp').read_bytes()).hexdigest(),'executable_sha256':hashlib.sha256((d/'generate_finite').read_bytes()).hexdigest()}
    if case=='missing_chunk':run['records']=[]
    if case=='bad_partition':run['records'][0]['end_exclusive']-=1
    if case=='wrong_mode':run['mode']='other'
    text=json.dumps(run)
    if case=='duplicate_json':text=text[:-1]+',"mode":"'+mode+'"}'
    if case=='nonfinite_json':text=text[:-1]+',"invalid":NaN}'
    (e/'RUN.json').write_text(text);cmd=[sys.executable,*opt,str(s/'scripts'/checker),'--study',str(study),'--scratch',str(scratch),'--run',name];t=time.monotonic();x=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(study/'stdout').write_bytes(x.stdout);(study/'stderr').write_bytes(x.stderr);passes=list((study/'evidence').glob('*-v2/RESULT.json'));passreceipt=any(json.loads(q.read_text()).get('status')in ['ALL_EXACT_CELL_ENCLOSURES_CHECKED','INDEPENDENT_ORDINARY_EXHAUSTIVE_CHECK_PASS']for q in passes)
    good=(x.returncode==0 and passreceipt)if case=='valid' else(x.returncode!=0 and not passreceipt)
    result={'id':label,'optimization':opt,'mode':mode,'checker':checker,'case':case,'expected_accept':case=='valid','exit_code':x.returncode,'passing_receipt':passreceipt,'control_pass':good,'wall_seconds':time.monotonic()-t};results.append(result)
    if not good:
     (o/'FAILED.json').write_text(json.dumps(result,indent=2)+'\n');raise RuntimeError('CLI control failed '+label)
result={'status':'ALL_ACTUAL_CLI_CONTROLS_PASS','cases':len(results),'script_hashes':{n:hashlib.sha256((s/'scripts'/n).read_bytes()).hexdigest()for n in ['numerical_records.py','check_exact_cells_v2.py','check_finite_independent_v2.py']},'records':results};t=o/'RESULT.tmp';t.write_text(json.dumps(result,indent=2)+'\n');t.replace(o/'RESULT.json');print(json.dumps({'status':result['status'],'cases':len(results)}))
