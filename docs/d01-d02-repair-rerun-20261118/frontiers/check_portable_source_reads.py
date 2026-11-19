"""Actual metadata CLIs on copied public sources, with original workspace reads denied.
This does not execute an ANT program or establish source-first PV.
"""
from pathlib import Path
import json,os,subprocess,sys,time,hashlib,shutil
from collect import O,load,need,pin,save

def main():
    root=Path(load(O/'portable-source-metadata-controls-v1/MATERIALIZATION_V8.json')['root']);analysis=root/'analysis';out=O/'portable-source-metadata-controls-v3';out.mkdir(exist_ok=False)
    # Copy the actual current pipeline versions. The public originals preserve
    # logical source identities; copied metadata outputs remain experiment-owned.
    names=['reviewed_literal_interfaces.py','REVIEWED_M_LITERAL_RECEIVER_INTERFACES_V1.json','REVIEWED_R_LITERAL_RECEIVER_INTERFACES_V1.json','source_resolver.py','collect.py','normalize.py','compare.py','premises.py','legacy_coordinate_parser_v1.py','build_premise_policy.py','check_interfaces.py','build_coverage.py','FROZEN_FINALIZATION_SELECTION.json','ALL24_SOURCE_BOUND_OBJECTS.json','NORMALIZED_OBJECTS.json','FINITE_EXPLICIT_FUNCTIONS.json','EXACT_ASSUMPTION_FORM_POLICY.json','ALL100_ASSUMPTION_FORMS_SOURCE_KEYS.json','NEW_EXACT_ASSUMPTION_FORMS.json','EXACT_BARE_INTERVAL_SOURCE_AXIS_POLICY.json']
    before=[pin(O/n)for n in names]
    for name in names:shutil.copy2(O/name,analysis/name)
    env=dict(os.environ,IEANTN_SOURCE_ROOT=str(root),IEANTN_SOURCE_MAP=str(root/'PUBLIC_SOURCE_MAP.json'),PYTHONPATH=str(root/'deny-original-workspace'),PYTHONDONTWRITEBYTECODE='1')
    records=[]
    for mode in [[],['-O'],['-OO']]:
        for label,tail in [('deny_probe',['-c',"try:\n open('/ryu/hyunsik/playground/independence/codex/ivy/AGENTS.md').read()\nexcept PermissionError as error:\n print('PASS_ACTUAL_ORIGINAL_WORKSPACE_OPEN_DENIAL')\nelse:\n raise ValueError('ORIGINAL_WORKSPACE_OPEN_WAS_NOT_DENIED')"]),('interfaces',[str(analysis/'check_interfaces.py'),'--check']),('source_collection',[str(analysis/'collect.py')]),('policy',[str(analysis/'build_premise_policy.py'),'--check'])]:
            argv=[sys.executable,*mode,'-B',*tail];start=time.monotonic();result=subprocess.run(argv,cwd=analysis,env=env,capture_output=True,text=True);tag=('normal'if not mode else mode[0][1:])+'-'+label;stdout=out/(tag+'.stdout');stderr=out/(tag+'.stderr');stdout.write_text(result.stdout);stderr.write_text(result.stderr);record={'label':tag,'argv':argv,'returncode':result.returncode,'elapsed_seconds':time.monotonic()-start,'stdout':pin(stdout),'stderr':pin(stderr)};records.append(record);save('PORTABLE_SOURCE_READS_PARTIAL.json',{'status':'RUNNING_METADATA_ONLY_PUBLIC_SOURCE_CLI_OPEN_DENIAL_CONTROLS','records':records,'source_pins':before})
            need(result.returncode==0,'PORTABLE_PUBLIC_SOURCE_CLI_FAILED '+tag+': '+result.stderr[-1000:])
            if label=='source_collection':need(hashlib.sha256((analysis/'ALL24_SOURCE_BOUND_OBJECTS.json').read_bytes()).hexdigest()==sha_current,'BYTE_IDENTICAL_LOGICAL_SOURCE_COLLECTION_FROM_PUBLIC_FILES')
    for old in before:need(pin(old['path'])==old,'CURRENT_CODE_AND_DATA_STABLE_DURING_PORTABLE_TESTS')
    save('ACTUAL_PORTABLE_SOURCE_NORMAL_O_OO_READ_DENIAL_CONTROLS.json',{'status':'PASS_TWELVE_ACTUAL_PUBLIC_SOURCE_METADATA_CLIS_NORMAL_O_OO_WITH_ORIGINAL_WORKSPACE_OPEN_DENIAL','source_pins':before,'public_source_map':pin(root/'PUBLIC_SOURCE_MAP.json'),'materialization':pin(O/'portable-source-metadata-controls-v1/MATERIALIZATION_V8.json'),'records':records,'source_collection_byteidentical':True,'new_scientific_execution':False,'original_mathematical_source_change':False,'final_complete_bundle_reconstruction_claimed':False})
    print('PASS12_ACTUAL_PUBLIC_SOURCE_METADATA_CLIS_NORMAL_O_OO_ORIGINAL_WORKSPACE_DENIED')
if __name__=='__main__':
    sha_current=hashlib.sha256((O/'ALL24_SOURCE_BOUND_OBJECTS.json').read_bytes()).hexdigest();main()
