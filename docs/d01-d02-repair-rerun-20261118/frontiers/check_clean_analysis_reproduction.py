"""One full portable metadata regeneration; original accepted snapshot immutable."""
from pathlib import Path
import os,json,hashlib,subprocess,sys,shutil,tempfile,time
from collect import O,need,pin,save

def main():
    source=Path('/data/ivy-final24-source-metadata-v2-v58fii9m');root=Path(tempfile.mkdtemp(prefix='ivy-final24-clean-analysis-',dir='/data'));mp=json.loads((source/'PUBLIC_SOURCE_MAP.json').read_text())
    for rec in mp['files'].values():
        old=source/rec['public_path'];target=root/rec['public_path'];target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(old,target)
    accepted=root/'frontiers';accepted.mkdir();working=root/'reproduction-work/frontiers';working.mkdir(parents=True)
    for p in O.iterdir():
        if p.is_file()and(p.suffix in ['.py','.json','.lock']or p.name.startswith('plot-requirements')):
            for target in [accepted/p.name,working/p.name]:shutil.copy2(p,target)
            mp['files'][str(p)]={'public_path':'frontiers/'+p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
    for rec in json.loads((O/'REQUIRED_ADDITIONAL_ANALYSIS_SOURCE_ASSETS_V1.json').read_text())['files']:
        original=Path(rec['path']);data=original.read_bytes();need(hashlib.sha256(data).hexdigest()==rec['sha256']and len(data)==rec['bytes'],'EXACT_ADDITIONAL_SOURCE_PIN');target=root/rec['archive_path'];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);mp['files'][str(original)]={'public_path':rec['archive_path'],'sha256':rec['sha256'],'bytes':rec['bytes']}
    mapfile=root/'PUBLIC_SOURCE_MAP.json';mapfile.write_text(json.dumps(mp,indent=2)+'\n');shutil.copytree(source/'deny-original-workspace',root/'deny-original-workspace')
    env=dict(os.environ,IEANTN_SOURCE_ROOT=str(root),IEANTN_SOURCE_MAP=str(mapfile),PYTHONPATH=str(root/'deny-original-workspace'),PYTHONDONTWRITEBYTECODE='1');argv=[sys.executable,'-B',str(working/'reproduce_analysis.py')];start=time.monotonic();r=subprocess.run(argv,cwd=working,env=env,capture_output=True,text=True);out=O/'clean-analysis-reproduction-v2';out.mkdir(exist_ok=False);(out/'stdout.log').write_text(r.stdout);(out/'stderr.log').write_text(r.stderr)
    need(r.returncode==0,'FULL_PORTABLE_METADATA_ANALYSIS_REGENERATION_FAILED '+r.stderr[-1500:]);current=json.loads((working/'FINITE_EXPLICIT_FUNCTIONS.json').read_text())['bounds'];original=json.loads((O/'FINITE_EXPLICIT_FUNCTIONS.json').read_text())['bounds'];need(current==original,'CLEAN_REGENERATION_EXACT_ALL15861_SOURCE_FUNCTION_BODIES')
    need(hashlib.sha256((working/'ALL24_SOURCE_BOUND_OBJECTS.json').read_bytes()).hexdigest()==pin(O/'ALL24_SOURCE_BOUND_OBJECTS.json')['sha256'],'CLEAN_SOURCE_COLLECTION_BYTEIDENTICAL')
    result={'status':'PASS_FULL_SEVEN_COMMAND_CLEAN_PORTABLE_ANALYSIS_REGENERATION_ALL15861_MATHEMATICAL_FUNCTION_BODIES_IDENTICAL_WITH_ORIGINAL_WORKSPACE_OPEN_DENIED','root':str(root),'argv':argv,'wall_seconds':time.monotonic()-start,'returncode':r.returncode,'source_map':pin(mapfile),'pipeline_receipt':{'path':str(working/'ACTUAL_SEQUENTIAL_ANALYSIS_REGENERATION.json'),'sha256':hashlib.sha256((working/'ACTUAL_SEQUENTIAL_ANALYSIS_REGENERATION.json').read_bytes()).hexdigest()},'accepted_original_data':pin(O/'FINITE_EXPLICIT_FUNCTIONS.json'),'working_output':{'path':str(working/'FINITE_EXPLICIT_FUNCTIONS.json'),'sha256':hashlib.sha256((working/'FINITE_EXPLICIT_FUNCTIONS.json').read_bytes()).hexdigest()},'relocation_changes_outer_provenance_paths_only':True,'original_mathematical_or_primary_experimental_outputs_changed':False,'new_scientific_execution_or_source_first_PV':False};save('ACTUAL_CLEAN_PORTABLE_ANALYSIS_REGENERATION.json',result);print(result['status'])
if __name__=='__main__':main()
