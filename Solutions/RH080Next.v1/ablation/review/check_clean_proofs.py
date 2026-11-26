#!/usr/bin/env python3
"""Strict completed portable169+15 proof-replay gate, independent of optimization."""
import argparse,math,re
from pathlib import Path
import run_review as common
import run_supplemental as generator
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
ALLOWED={'propext','Classical.choice','Quot.sound'}
BAD=re.compile(r'PANIC|sorryAx|(?m:^|:)\s*error(?::|\()')


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    run=args.run;common.need((run/'RESULT.json').is_file(),'Missing completed portable proof result')
    plan=common.load(run/'PLAN.json');result=common.load(run/'RESULT.json')
    common.need(result['status']=='PASS_PORTABLE_COMMON169_PLUS_ALL13_LOCKED15_LEAN_SOURCE_COLD_STD3','Incomplete portable proof status')
    common.need(result['original_application_object_fallback'] is False and plan['original_application_objects_used'] is False,'Application proof object cache used')
    common.need(result['external_model_inference_calls']==result['primary_successes_added']==0 and result['original_primary_outcomes_unchanged'] is True,'Unexpected research or primary promotion')
    common.need(result['common_modules']==169 and result['locked_trials']==13 and result['locked_source_modules']==15 and result['compile_commands']==199,'Incomplete exact169+15+15 coverage')
    common.need(len(result['commands'])==len({r['label']for r in result['commands']})==199,'Collapsed compiler identities')
    inventory=common.load(HERE/'COMMON169_SOURCE_INPUTS.json');expected={r['module']:r for r in inventory['modules']}
    common.need(len(expected)==169 and {r['module']for r in plan['source_rows']}==set(expected) and len(plan['source_rows'])==169,'Common169 population differs')
    common.need(plan['controller_sha256']==common.sha(HERE/'reproduce_clean_proofs.py')==common.sha(run/'reproduce_clean_proofs.executed.py'),'Executed clean controller differs')
    for row in plan['source_rows']:
        n=row['module'];written=expected[n];p=REPO/written['source'];snapshot=run/'common/source'/(n.replace('.','/')+'.lean')
        common.need(row['sha256']==written['sha256']==common.sha(p)==common.sha(snapshot),'Pinned common source differs '+n)
        common.need(row['source']==written['source'] and row['imports']==written['imports'],'Common written declaration/import identity differs')
    module_files={r['module']:run/'common/source'/(r['module'].replace('.','/')+'.lean')for r in plan['source_rows']}
    required_labels={n.replace('.','_'):dict(module=n,path=path,object=run/'common/objects'/(n.replace('.','/')+'.olean'))for n,path in module_files.items()}
    wanted_payloads={p.name:p for p in (HERE/'supplemental_evidence_v1/locked_payloads').iterdir() if p.is_dir()}
    common.need(len(plan['payload_rows'])==13 and {r['trial']for r in plan['payload_rows']}==set(wanted_payloads),'Omitted exact locked row')
    for row in plan['payload_rows']:
        trial=row['trial'];root=wanted_payloads[trial];lock=common.load(root/'LOCK.json')
        common.need(row['primary_eligible'] is False and row['lock_sha256']==common.sha(root/'LOCK.json'),'Primary lock/status differs')
        modules={Path(r['path']).stem:r for r in lock['files'] if r['path'].endswith('.lean')}
        common.need(set(row['modules'])==set(modules) and len(row['modules'])==len(modules),'Omitted exact locked module')
        for module,entry in modules.items():
            source=run/'trials'/trial/'source'/(module+'.lean')
            common.need(common.sha(source)==entry['sha256']==common.sha(root/entry['path']),'Locked Lean bytes changed')
            for name in [module,'IndependentAudit_'+module]:
                required_labels[trial+'-'+name]=dict(module=name,path=run/'trials'/trial/'source'/(name+'.lean'),object=run/'trials'/trial/'objects'/(name+'.olean'))
            audit_source=run/'trials'/trial/'source'/('IndependentAudit_'+module+'.lean')
            expected_audit=generator.generic_audit(module).replace('/work/submission/EXPORT.'+module+'.json',str(audit_source.resolve().parent/('EXPORT.'+module+'.json')))
            common.need(audit_source.read_text()==expected_audit,'Full-module axiom/type audit source differs')
            export_path=run/'trials'/trial/'source'/('EXPORT.'+module+'.json');export=common.load(export_path)
            common.need(export['module']==module and export['theorems']>0 and not export['problems'],'Missing submitted module proof export')
            common.need(len(export['declarations'])==len({d['declaration']for d in export['declarations']}),'Collapsed submitted declaration identities')
            for declaration in export['declarations']:
                common.need(declaration['type'] and declaration['kind']!='axiom' and set(declaration['axioms'])<=ALLOWED,'Nonstandard submitted proof axiom')
    common.need(set(required_labels)=={r['label']for r in result['commands']},'Compiler routes differ from complete169+15+15 scope')
    peaks=[]
    for record in result['commands']:
        label=record['label'];expected=required_labels[label];common.need(record==common.load(run/(label+'.COMPILED.json')),'Completed compiler receipt association differs')
        common.need(record['module']==expected['module'] and record['returncode']==0 and record['strict_accepted'] is True,'Compiler failed')
        common.need(type(record['seconds'])in[int,float] and math.isfinite(record['seconds']) and record['seconds']>0,'Invalid execution time')
        common.need(record['source_sha256']==common.sha(expected['path']) and record['object_sha256']==common.sha(expected['object']),'Source/proof object receipt differs')
        for ext in ['stdout','stderr','time']:
            path=run/'logs'/(label+'.'+ext);common.need(record[ext+'_sha256']==common.sha(path),'Compiler log differs')
            if ext!='time':common.need(BAD.search(path.read_text()) is None,'Compiler diagnostics rejected')
        timing=(run/'logs'/(label+'.time')).read_text();rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',timing)
        common.need(len(rss)==1 and 'Command terminated by signal'not in timing and re.search(r'Exit status: 0\s*$',timing) is not None,'Compiler timing/termination failed')
        peaks.append(int(rss[0])*1024)
    common.need(result['failed_compilers']==result['SIGKILL_compilers']==0 and result['max_child_RSS_bytes']==max(peaks),'Compiler/resource summary differs')
    samples=common.load(run/'SAMPLED_RESOURCES.json');ss=samples['samples'];common.need(ss and not samples['resource_failures'],'Missing/interrupted resource samples')
    common.need(result['sampled_group_max_RSS_bytes']==max(r['RSS_bytes']for r in ss),'Sampled group RSS differs')
    common.need(result['min_sampled_MemAvailable_bytes']==min(r['MemAvailable_bytes']for r in ss)>=256*2**30,'Host reserve violated')
    common.need(max(r['campaign_scratch_bytes']for r in ss)<plan['scratch_stop_bytes']<=290*2**30,'Campaign scratch reserve violated')
    common.save(args.output,dict(status='PASS_INDEPENDENT_COMPLETED_PORTABLE169_COMMON15_LOCKED_PROOF_REPLAY',
        common_modules=169,locked_trials=13,locked_source_modules=15,compiler_routes=199,
        result_sha256=common.sha(run/'RESULT.json'),plan_sha256=common.sha(run/'PLAN.json'),
        validator_sha256=common.sha(Path(__file__)),new_primary_successes=0,
        scope='Separate clean mathematical proof replay, not primary matched-runtime reclassification'))
    print('PASS independent complete169+15+15 source-cold proof replay')


if __name__=='__main__':main()
