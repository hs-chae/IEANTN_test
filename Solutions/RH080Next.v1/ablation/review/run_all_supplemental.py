#!/usr/bin/env python3
"""Replay all13 censored locked payloads; no new inference or primary reclassification."""
import argparse,concurrent.futures,json,subprocess,sys,time,shutil
from pathlib import Path
import run_review as common
import run_supplemental as worker

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    common.need(a.out.resolve().is_relative_to(worker.ROOT) and not a.out.exists(),'Fresh owned batch path required')
    plan=common.load(common.D/'EXPOSURE_CENSORED_SUPPLEMENTAL_PLAN.json');rows=plan['rows'];common.need(len(rows)==13,'Exact13 censored population required')
    memory=int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024
    common.need(memory>=256*2**30+4*64*2**30,'Host reserve plus4offlineworkers unavailable')
    common.need(shutil.disk_usage(a.out.parent).free>=2**40,'Independent1TiBfree disk required')
    pilot=worker.ROOT/'fixed_width-C_network-r1-v3';pilotReview=common.load(pilot/'submission/REVIEW.json');common.need(pilotReview['status']=='ALL_LOCKED_LEAN_MODULES_COMPILED_AND_STD3_EXPORTED','Corrected two-module pilot not ready')
    pilotInputs=common.load(pilot.with_name(pilot.name+'.INPUTS.json'));common.need(pilotInputs['controller_sha256']==common.sha(Path(worker.__file__)) and pilotInputs['common_runtime_sha256']==worker.RUNTIME_SHA,'Pilot changed conditions')
    a.out.mkdir(parents=True);common.save(a.out/'PLAN.json',dict(status='FROZEN_ALL13_SUPPLEMENTAL_POSTHOC_PLAN',primary_eligible=False,primary_results_changed=False,external_model_inference_calls=0,universe=[r['trial'] for r in rows],same_original_common_runtime=str(worker.RUNTIME),runtime_sha256=worker.RUNTIME_SHA,controller_sha256=common.sha(Path(worker.__file__)),coordinator_sha256=common.sha(Path(__file__)),workers=4,memory_gib_each=64,scratch_gib_each=12,cpus_each=4,MemAvailable_bytes=memory,wall_seconds_each=1200,corrected_pilot_reused=str(pilot)))
    def run(row):
        trial=row['trial']
        if trial=='fixed_width-C_network-r1':return dict(trial=trial,out=str(pilot),reused_exact_corrected_pilot=True,returncode=0)
        out=worker.ROOT/(trial+'-v3');command=[sys.executable,str(Path(worker.__file__)),'--trial',trial,'--out',str(out)];start=time.monotonic()
        with (a.out/(trial+'.stdout')).open('xb') as o,(a.out/(trial+'.stderr')).open('xb') as e:p=subprocess.run(command,stdout=o,stderr=e)
        return dict(trial=trial,out=str(out),reused_exact_corrected_pilot=False,command=command,returncode=p.returncode,seconds=time.monotonic()-start)
    results=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for future in concurrent.futures.as_completed([pool.submit(run,r) for r in rows]):
            record=future.result();results.append(record);print(record['trial'],record['returncode'],flush=True)
            temp=a.out/'PROGRESS.pending';temp.write_text(json.dumps(dict(completed=len(results),total=13,rows=results),indent=2)+'\n');temp.replace(a.out/'PROGRESS.json')
    common.save(a.out/'RESULT.json',dict(status='ALL13_SUPPLEMENTAL_EXECUTIONS_FINISHED_CLAIM_INTERPRETATION_PENDING',rows=results,primary_eligible=False,primary_results_changed=False,external_model_inference_calls=0))

if __name__=='__main__':main()
