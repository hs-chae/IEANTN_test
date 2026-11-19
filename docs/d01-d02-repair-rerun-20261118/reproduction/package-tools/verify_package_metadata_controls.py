"""Actual source-only CLIs. Never build a study or fixture package."""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,subprocess,sys
A=Path(__file__).resolve().parent
def need(x,m):
 if not x:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--inventory',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh controls');a.out.mkdir()
 spec=importlib.util.spec_from_file_location('inventory',A/'prepare_inventory.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 fixture=a.out/'fixture.txt';fixture.write_bytes(b'public metadata fixture only\n')
 asset={'source_path':str(fixture.resolve()),'archive_path':'fixture.txt','sha256':sha(fixture.read_bytes()),'size':fixture.stat().st_size,'privacy':m.inspect_bytes(fixture.name,fixture.read_bytes()),'gzip_json':False}
 base={'schema':'PUBLIC_EVIDENCE_SOURCE_INVENTORY_DRAFT_V1','assets':[asset],'pending_required_assets_and_joins':[],'privacy_flagged_assets':[]};cases=[]
 cases.append(('duplicate','{"schema":"wrong",'+json.dumps(base)[1:]))
 for token in ['NaN','Infinity','1e9999']:cases.append(('nonfinite-'+token,json.dumps(base)[:-1]+',"extra":'+token+'}'))
 for n in ['../fixture.txt','./fixture.txt','/fixture.txt','a//fixture.txt','a\\fixture.txt']:
  z=copy.deepcopy(base);z['assets'][0]['archive_path']=n;cases.append(('unsafe-'+str(len(cases)),json.dumps(z)))
 z=copy.deepcopy(base);z['assets'][0]['sha256']='0'*64;cases.append(('changed-source',json.dumps(z)))
 z=copy.deepcopy(base);q=copy.deepcopy(asset);q['archive_path']='fixture.txt/child';z['assets'].append(q);cases.append(('file-parent-collision',json.dumps(z)))
 z=copy.deepcopy(base);z['assets'][0]['gzip_json']='false';cases.append(('compression-not-boolean',json.dumps(z)))
 z=copy.deepcopy(base);q=copy.deepcopy(asset);q['archive_path']='data.json';q['gzip_json']=True;z['assets']=[q,dict(q,archive_path='data.json.gz',gzip_json=False)];cases.append(('compressed-destination-collision',json.dumps(z)))
 rows=[]
 for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  for label,path,ok in [('actual-current-inventory',a.inventory,True)]+[(name,None,False) for name,_ in cases]:
   d=a.out/(mode+'-'+label);d.mkdir()
   if path is None:path=d/'inventory.json';path.write_text(dict(cases)[label])
   argv=[sys.executable,'-I','-B',*flags,str(A/'package_evidence.py'),'--inventory',str(path.resolve()),'--check'];r=subprocess.run(argv,capture_output=True)
   (d/'stdout').write_bytes(r.stdout);(d/'stderr').write_bytes(r.stderr);need((r.returncode==0)==ok,'actual metadata CLI '+mode+' '+label)
   rows.append({'mode':mode,'case':label,'argv':argv,'returncode':r.returncode,'expected_success':ok,'stdout_sha256':sha(r.stdout),'stderr_sha256':sha(r.stderr)})
 result={'status':'PASS_ACTUAL_PACKAGE_METADATA_NORMAL_O_OO','inventory':{'path':str(a.inventory.resolve()),'sha256':sha(a.inventory.read_bytes())},'sources':{n:sha((A/n).read_bytes()) for n in ['prepare_inventory.py','package_evidence.py','verify_package_metadata_controls.py']},'rows':rows,'actual_study_or_fixture_packages_built':0,'models_scopes_compilers_numerics':0}
 with (a.out/'RESULT.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
 print(json.dumps({'status':result['status'],'actual_CLIs':len(rows),'result_sha256':sha((a.out/'RESULT.json').read_bytes())},sort_keys=True))
if __name__=='__main__':main()
