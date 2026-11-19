"""Regenerate this pinned comparative analysis only, in sequential checked steps.
No ANT workload, scientific compiler, model, dependency install or plot is run.
"""
from collect import O,load,need,pin,save
from pathlib import Path
import subprocess,sys,time

def main():
    out=O/'analysis-regeneration-runs';out.mkdir(exist_ok=True);i=1
    while (out/str(i)).exists():i+=1
    work=out/str(i);work.mkdir();sources=['reviewed_literal_interfaces.py','REVIEWED_M_LITERAL_RECEIVER_INTERFACES_V1.json','REVIEWED_R_LITERAL_RECEIVER_INTERFACES_V1.json','source_resolver.py','build_coverage.py','collect.py','FROZEN_FINALIZATION_SELECTION.json','build_premise_policy.py','premises.py','normalize.py','legacy_coordinate_parser_v1.py','EXACT_BARE_INTERVAL_SOURCE_AXIS_POLICY.json','compare.py','paired_ratios.py','check_interfaces.py']
    record={'status':'RUNNING_SEQUENTIAL_PINNED_METADATA_ANALYSIS_REGENERATION','sources':[pin(O/n)for n in sources],'commands':[],'scientific_execution':False}
    commands=[['collect.py'],['build_premise_policy.py'],['normalize.py'],['compare.py','--data-only'],['paired_ratios.py'],['check_interfaces.py','--check'],['build_coverage.py']]
    for j,cmd in enumerate(commands):
        args=[sys.executable,'-B',str(O/cmd[0]),*cmd[1:]];st=time.monotonic();r=subprocess.run(args,cwd=O,capture_output=True,text=True)
        stdout=work/(str(j)+'.stdout');stderr=work/(str(j)+'.stderr');stdout.write_text(r.stdout);stderr.write_text(r.stderr)
        record['commands'].append({'argv':args,'returncode':r.returncode,'wall_seconds':time.monotonic()-st,'stdout':pin(stdout),'stderr':pin(stderr)})
        (work/'PARTIAL.json').write_text(__import__('json').dumps(record,indent=2)+'\n')
        need(r.returncode==0,'SEQUENTIAL_REGENERATION_STOPPED '+cmd[0]+':'+r.stderr[-1000:])
    for source in record['sources']:need(pin(source['path'])==source,'FROZEN_SOURCE_VERSION_DURING_SEQUENTIAL_REGENERATION')
    record.update(status='PASS_SEQUENTIAL_SOURCE_COLLECTION_NORMALIZATION_COMPARISON_METADATA_REGENERATION',outputs=[pin(O/n)for n in ['ALL24_SOURCE_BOUND_OBJECTS.json','NORMALIZED_OBJECTS.json','FINITE_EXPLICIT_FUNCTIONS.json','MATCHED_R_COEFFICIENT_VECTOR_TABLE.json','WHOLE_SYMBOLIC_OPERATOR_FRONTIERS.json','SAME_ONSET_DIAGNOSTIC_FUNCTION_VALUES.json','EXACT_SOURCE_PAIRED_M_FUNCTION_RATIO_CHECKS.json']])
    (work/'RESULT.json').write_text(__import__('json').dumps(record,indent=2)+'\n');save('ACTUAL_SEQUENTIAL_ANALYSIS_REGENERATION.json',{'receipt':pin(work/'RESULT.json'),'status':record['status']});print(record['status'])
if __name__=='__main__':main()
