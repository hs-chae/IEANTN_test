#!/usr/bin/env python3
"""Actual CLI tests of resource-journal gates, not numerical proof acceptance.

Fixtures intentionally contain no Lean objects or mathematical certificates.
The separate real N=1000 clean smoke must exercise the executable engine.
"""
from pathlib import Path
import argparse
import copy
import importlib.util
import json
import os
import subprocess
import sys

HERE=Path(__file__).resolve().parent
# Local source review uses the unchanged pinned parser. The portable wrapper
# places that same parser beside the engine in its actual execution directory.
legacy=HERE.parents[1]/'portable/scripts'
if legacy.is_dir():sys.path.insert(0,str(legacy))
spec=importlib.util.spec_from_file_location('physical_engine',HERE/'reproduce_physical_closure.py')
E=importlib.util.module_from_spec(spec);spec.loader.exec_module(E)
CASES=['positive-three-128GiB-AS','positive-heavy-alone','boolean-AS','float-forecast',
       'insufficient-available','missing-active-observation','wrong-growth','wrong-AS-total',
       'wrong-observed-peak','missing-release','duplicate-dispatch','heavy-overlap',
       'float-safety-factor','boolean-resource-sample','duplicate-json','overflow-json']
POSITIVE={'positive-three-128GiB-AS','positive-heavy-alone'}
GATES={'boolean-AS':'actual module AS limit','float-forecast':'strict physical admission metadata',
 'insufficient-available':'each actual admission preserves reserve plus potential growth',
 'missing-active-observation':'all active worker observations',
 'wrong-growth':'each actual admission preserves reserve plus potential growth',
 'wrong-AS-total':'at most22 actual workers, AS sum informational only',
 'wrong-observed-peak':'observed completed child peak','missing-release':'complete actual dispatch and drain',
 'duplicate-dispatch':'unique actual dispatch','heavy-overlap':'heavy profiles run alone',
 'float-safety-factor':'exact RSS forecasting rule',
 'boolean-resource-sample':'actual compiler-tree aggregate sample',
 'duplicate-json':'duplicate JSON key','overflow-json':'nonfinite JSON number'}
G=1<<30

def fixture(out,heavy=False):
    names=['A','B','C'] if not heavy else ['Final']
    cap=128*G if not heavy else 256*G
    records=[{'module':n,'memory_limit_bytes':cap,'peak_rss_bytes':32*G}for n in names]
    plan={'resource_scheduler':'PHYSICAL_RSS_FORECAST_V1','max_parallel_workers':22,
          'host_reserve_bytes':512*G,'per_task_address_space_ceiling_bytes':300*G,
          'initial_physical_forecast_bytes':E.INITIAL_FORECAST,
          'completed_peak_safety_factor':[6,5],
          'heavy_exclusive_address_threshold_bytes':E.HEAVY_THRESHOLD}
    events=[];active={};peak=0
    for n in names:
        snapshots=[{'module':k,'pid':None,'start_ticks':None,'observed_RSS_bytes':0,
                    'physical_forecast_bytes':E.physical_forecast(v,peak),
                    'potential_growth_bytes':E.physical_forecast(v,peak)}for k,v in active.items()]
        budget=E.physical_forecast(cap,peak);growth=sum(x['potential_growth_bytes']for x in snapshots)
        events.append({'event':'reserve_before_submit','module':n,'module_address_limit_bytes':cap,
             'physical_forecast_bytes':budget,'completed_peak_RSS_bytes':peak,
             'host_reserve_bytes':512*G,'MemAvailable_bytes':2*(1<<40),
             'active':snapshots,'active_potential_growth_bytes':growth,
             'required_available_bytes':512*G+growth+budget,'running_workers_before':len(active),
             'running_workers_after':len(active)+1,'running_address_limits_before_bytes':sum(active.values()),
             'running_address_limits_after_bytes':sum(active.values())+cap,'unix':0})
        active[n]=cap
    for n in names:
        active.pop(n);peak=32*G
        events.append({'event':'release_after_completion','module':n,'module_address_limit_bytes':cap,
             'actual_peak_RSS_bytes':32*G,'completed_peak_RSS_bytes':peak,
             'running_workers_after':len(active),'running_address_limits_after_bytes':sum(active.values()),'unix':1})
    samples=[{'unix':0,'MemAvailable_bytes':2*(1<<40),'owned_compiler_tree_RSS_bytes':0,
              'owned_regular_disk_bytes':0,'active':[]}]
    result={'resource_scheduler':'PHYSICAL_RSS_FORECAST_V1','records':records,
            'sampled_peak_owned_compiler_tree_RSS_bytes':0}
    return plan,result,events,samples

def execute(case,out):
    plan,result,events,samples=fixture(out,case=='positive-heavy-alone')
    if case=='boolean-AS':events[0]['module_address_limit_bytes']=True
    elif case=='float-forecast':events[0]['physical_forecast_bytes']=float(events[0]['physical_forecast_bytes'])
    elif case=='insufficient-available':events[0]['MemAvailable_bytes']=events[0]['required_available_bytes']-1
    elif case=='missing-active-observation':events[1]['active']=[]
    elif case=='wrong-growth':events[1]['active_potential_growth_bytes']=0
    elif case=='wrong-AS-total':events[2]['running_address_limits_after_bytes']=128*G
    elif case=='wrong-observed-peak':events[3]['actual_peak_RSS_bytes']=1
    elif case=='missing-release':events.pop()
    elif case=='duplicate-dispatch':events.insert(1,copy.deepcopy(events[0]))
    elif case=='heavy-overlap':
        events[1]['module_address_limit_bytes']=256*G;result['records'][1]['memory_limit_bytes']=256*G
        events[1]['physical_forecast_bytes']=256*G
        events[1]['required_available_bytes']=512*G+events[1]['active_potential_growth_bytes']+256*G
        events[1]['running_address_limits_after_bytes']=128*G+256*G
    elif case=='float-safety-factor':plan['completed_peak_safety_factor']=[6.0,5.0]
    elif case=='boolean-resource-sample':samples[0]['owned_compiler_tree_RSS_bytes']=False
    schedule=''.join(json.dumps(x)+'\n'for x in events)
    if case=='duplicate-json':schedule=schedule.replace('{','{"event":"duplicate",',1)
    if case=='overflow-json':schedule=schedule.replace('"unix": 0','"unix": 1e400',1)
    (out/'SCHEDULE.jsonl').write_text(schedule)
    (out/'RESOURCE_SAMPLES.jsonl').write_text(''.join(json.dumps(x)+'\n'for x in samples))
    result['RESOURCE_SAMPLES_sha256']=E.sha(out/'RESOURCE_SAMPLES.jsonl')
    E.validate_physical_journal(out,plan,result)
    if case=='positive-three-128GiB-AS':
        E.need(max(x['running_address_limits_after_bytes']for x in events)>300*G,
               'positive fixture really exceeds old AS sum without exceeding its physical forecast')

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--case',choices=CASES)
    p.add_argument('--out',required=True,type=Path);a=p.parse_args();out=a.out.resolve()
    E.need(not out.exists() and out.parent.is_dir(),'fresh experiment-owned resource test directory')
    out.mkdir()
    if a.case:execute(a.case,out);print('RESOURCE_GATE_ACCEPTED');return
    rows=[]
    for opt in [[],['-O'],['-OO']]:
        for case in CASES:
            q=out/(str(len(rows))+'-'+case);cmd=[sys.executable,*opt,str(Path(__file__).resolve()),'--case',case,'--out',str(q)]
            cp=subprocess.run(cmd,capture_output=True,text=True)
            for n,t in [('stdout',cp.stdout),('stderr',cp.stderr)]: (out/(str(len(rows))+'.'+n)).write_text(t)
            E.need((cp.returncode==0)==(case in POSITIVE),'unexpected actual resource CLI decision:'+case)
            if case in POSITIVE:
                E.need(cp.stdout.strip()=='RESOURCE_GATE_ACCEPTED','actual positive helper output')
            else:
                E.need(GATES[case] in cp.stderr,'specific expected rejection gate:'+case)
            rows.append({'case':case,'optimization':opt,'command':cmd,'returncode':cp.returncode,
                         'expected_acceptance':case in POSITIVE,'expected_gate':GATES.get(case),
                         'stdout_sha256':E.sha(out/(str(len(rows))+'.stdout')),
                         'stderr_sha256':E.sha(out/(str(len(rows))+'.stderr'))})
    E.atomic(out/'RESULT.json',{'status':'PASS_48_ACTUAL_RESOURCE_JOURNAL_HELPER_CONTROLS',
             'engine_sha256':E.sha(HERE/'reproduce_physical_closure.py'),'test_sha256':E.sha(__file__),
             'rows':rows,'scope':'Synthetic resource-only journal fixtures exercising active real reader gates. Not Lean/numerical proof acceptance, actual execution resource measurements, or the separate N1000 clean source smoke.'})
    print('PASS_48_ACTUAL_RESOURCE_JOURNAL_HELPER_CONTROLS')
if __name__=='__main__':main()
