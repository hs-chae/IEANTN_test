#!/usr/bin/env python3
"""Validate all13 exact locked censored mathematical payload type exports.

This validates compilation, declared-type/Std3 coverage, source provenance and
common-runtime conditions. It does not decide mathematical novelty or convert
any original inadmissible trial into a primary success.
"""
import argparse,json,os,re
from pathlib import Path
import run_review as common
import run_supplemental as generator
D=common.D
ALLOWED={'propext','Classical.choice','Quot.sound'}


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--runs',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args()
    primary_path=D/'exposure-matched-v2/EXPOSURE_RESEARCH_EXECUTION.json';primary=common.load(primary_path);preflight=common.load(D/'EXPOSURE_CENSORED_SUPPLEMENTAL_PLAN.json');recovery_path=D/'exposure-supplemental-recovery-v1/RESULT.json';recovery=common.load(recovery_path)
    wanted={r['trial'] for r in primary['rows'] if not r['discovery_admissible_for_evaluation']};common.need(len(primary['rows'])==16 and len(wanted)==13,'Original primary population differs')
    runs=common.load(a.runs)['rows'];common.need(len(runs)==len({r['trial'] for r in runs})==13 and {r['trial'] for r in runs}==wanted,'Requested entire13 source universe differs')
    common.need(recovery['primary_summary_sha256']==common.sha(primary_path),'Recovery primary identity differs');rows=[]
    for chosen in runs:
        trial=chosen['trial'];run=Path(chosen['out']);export=run/'submission';outer=common.load(run/'result.json');inputs=common.load(run.with_name(run.name+'.INPUTS.json'));review=common.load(export/'REVIEW.json')
        original=D/'exposure-controller-v2/trials'/trial/'research-v1';locked=common.load(original/'submission/LOCK.json');lock_sha=common.sha(original/'submission/LOCK.json');historical=next(r for r in primary['rows'] if r['trial']==trial)
        exact=next(r for r in recovery['rows'] if r['trial']==trial);source_root=Path(exact['recovered_directory'])
        common.need(lock_sha==exact['lock_sha256']==inputs['primary_lock_sha256']==next(r for r in preflight['rows'] if r['trial']==trial)['lock_sha256'],'Written lock identity differs')
        common.need(common.sha(original/'result.json')==historical['result_sha256']==inputs['primary_result_sha256'],'Original primary outcome changed')
        common.need(historical['discovery_admissible_for_evaluation'] is False and historical['stop_reason']=='GENERATED_OUTPUT_ADMISSION_CEILING','Original eligibility changed')
        for artifact in exact['artifacts']:
            actual=original/'submission'/artifact['path'];digest=common.sha(actual) if actual.is_file() else None
            common.need(digest==artifact['original_submission_sha256'],'Original archived export bytes changed')
            common.need(common.sha(source_root/artifact['path'])==artifact['sha256'],'Recovered exact LOCK bytes changed')
        common.need(outer['mode']=='NOAUTH_FINAL_CONFIG_FIXTURE' and outer['stop_reason'] is None and outer.get('infrastructure_error') is None,'Incomplete offline scripted review')
        common.need(outer['credentials_mounted_in_worker'] is False and outer['private_reasoning_collected'] is False,'Offline review boundary differs')
        common.need(outer['limits']['memory_gib']==64 and outer['limits']['scratch_gib']==12 and outer['limits']['cpus']==4,'Supplemental resource policy differs')
        common.need(inputs['common_runtime_sha256']==generator.RUNTIME_SHA and common.sha(generator.RUNTIME)==generator.RUNTIME_SHA,'Not richest original commonD runtime')
        common.need(inputs['external_model_inference_calls']==review['external_model_inference_calls']==0 and review['primary_eligible'] is False,'Unexpected research or reclassification')
        for key in ['host_absent','auth_absent','controller_canary_absent','genericLean_available']:common.need(review['isolation'][key] is True,'Isolation probe failed')
        common.need(review['isolation']['pid_namespace']!=os.readlink('/proc/self/ns/pid') and review['isolation']['net_namespace']!=os.readlink('/proc/self/ns/net'),'Namespace boundary differs')
        export_lock=export/'LOCK.json';common.need(outer['artifact_export']['consistent'] is True and common.sha(export_lock)==outer['artifact_export']['lock_sha256'],'Actual export lock incomplete')
        items=common.load(export_lock)['files'];common.need(len(items)==len({r['path'] for r in items}),'Duplicate actual export identities')
        for item in items:
            p=export/item['path'];common.need(p.name==item['path'] and p.is_file() and not p.is_symlink() and common.sha(p)==item['sha256'],'Actual exported evidence changed')
        modules={Path(r['path']).stem:r for r in locked['files'] if r['path'].endswith('.lean')};common.need(set(review['source_modules'])==set(modules) and len(review['source_modules'])==len(modules),'Missing actual submitted module')
        records=review['records'];common.need(len(records)==2*len(modules) and review['status']=='ALL_LOCKED_LEAN_MODULES_COMPILED_AND_STD3_EXPORTED','Source compile/export incomplete')
        count=0;theorems=0;files=[]
        for module,source in modules.items():
            common.need(common.sha(export/source['path'])==source['sha256']==inputs['source_sha256'][module]==review['source_sha256'][module],'Not exact original LOCK Lean source')
            audit=export/('IndependentAudit_'+module+'.lean');common.need(audit.read_text()==generator.generic_audit(module),'Full-module independent audit changed')
            table=common.load(export/('EXPORT.'+module+'.json'));names=[r['declaration'] for r in table['declarations']]
            common.need(len(names)==len(set(names)) and len(names)>0 and table['theorems']>0 and not table['problems'],'Collapsed/empty/nonStd3 export')
            for declaration in table['declarations']:
                common.need(declaration['type'] and declaration['kind']!='axiom' and set(declaration['axioms'])<=ALLOWED,'Unverified submitted declaration')
            common.need(sum(r['kind']=='theorem' for r in table['declarations'])==table['theorems'],'Theorem census differs')
            count+=len(names);theorems+=table['theorems'];files.append(dict(file=source['path'],source_sha256=source['sha256'],type_export_sha256=common.sha(export/('EXPORT.'+module+'.json')),theorems=table['theorems'],declarations=len(names)))
        common.need([r['module'] for r in records]==[n for m in review['source_modules'] for n in [m,'IndependentAudit_'+m]],'Compiler/audit route order differs')
        for record in records:
            name=record['module'];common.need(record['exitcode']==0 and record['strict_compile_accepted'] is True and record['object_sha256'] is not None,'Missing actual accepted proof object')
            stdout=export/(name+'.stdout');stderr=export/(name+'.stderr');common.need(common.sha(stdout)==record['stdout_sha256'] and common.sha(stderr)==record['stderr_sha256'],'Actual compiler log differs')
            common.need(not re.search(r'PANIC|sorryAx|(?m:^|:)\s*error(?::|\()',stdout.read_text()+stderr.read_text()),'Strict compiler diagnostics rejected')
            if name.startswith('IndependentAudit_'):common.need('SUPPLEMENTAL_FULL_'+name.removeprefix('IndependentAudit_')+'_TYPE_STD3_EXPORT_PASS' in stdout.read_text(),'Actual full-module audit marker missing')
        rows.append(dict(trial=trial,status='EXACT_LOCK_ALL_MODULES_COMPILED_FULL_TYPES_STD3_EXPORTED_NOT_MATH_NOVELTY_GATE',primary_eligible=False,primary_lock_sha256=lock_sha,primary_result_sha256=inputs['primary_result_sha256'],source_files=files,theorems=theorems,declarations=count,run=str(run),runtime_sha256=generator.RUNTIME_SHA,review_sha256=common.sha(export/'REVIEW.json'),export_lock_sha256=common.sha(export_lock),backend_result_sha256=common.sha(run/'result.json'),inputs_sha256=common.sha(run.with_name(run.name+'.INPUTS.json')),executed_controller_sha256=inputs['controller_sha256'],claim_interpretation_pending=True))
    result=dict(status='PASS_ALL13_EXACT_LOCK_CENSORED_PAYLOADS_FULL_MODULE_COMPILE_TYPES_STD3',rows=rows,source_modules=sum(len(r['source_files']) for r in rows),theorems=sum(r['theorems'] for r in rows),declarations=sum(r['declarations'] for r in rows),primary_eligible_count=0,original_primary_admissible_count=3,original_primary_censored_count=13,primary_summary_sha256=common.sha(primary_path),recovery_sha256=common.sha(recovery_path),runtime_sha256=generator.RUNTIME_SHA,validator_sha256=common.sha(Path(__file__)),external_model_inference_calls=0,scope='SUPPLEMENTAL_MATH_INTERPRETATION_SEPARATE_NO_CAUSAL_ADVANTAGE_NO_PRIMARY_RECLASSIFICATION')
    common.save(a.output,result);print('PASS all13 exact locked payloads; modules='+str(result['source_modules'])+' theorems='+str(result['theorems'])+' full_declarations='+str(result['declarations']))

if __name__=='__main__':main()
