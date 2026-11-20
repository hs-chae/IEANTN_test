#!/usr/bin/env python3
"""Derived actual resource/axiom summary of the closed ORIGINAL full scalar grid."""
from pathlib import Path
import argparse,hashlib,json,re
from execute_full_scalar_certificate import validate,read,need,sha

def metric(text,label):
 m=re.search(re.escape(label)+r':\s*([0-9.]+)',text);need(m is not None,'actual GNU-time metric '+label);return float(m[1])
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--result',type=Path,required=True);p.add_argument('--sampling',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh summary');verified=validate(a.result);d=read(a.result);need(d['rows']==1755663 and d['stop']==1490000000001 and d['full_locked_prefix'] is True,'entire original fixed prefix');rows=[]
 for record in d['records']:
  receipt=Path(record['receipt']);r=read(receipt);text=(receipt.parent/'rusage.txt').read_text();rows.append(dict(module=record['module'],seconds=r['elapsed_seconds'],peak_rss_bytes=int(metric(text,'Maximum resident set size (kbytes)'))*1024,cpu_seconds=metric(text,'User time (seconds)')+metric(text,'System time (seconds)'),source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],receipt=str(receipt),receipt_sha256=sha(receipt)))
 s=read(a.sampling);need(s['status']=='MIDRUN_SAMPLED_OBSERVATION_NOT_WHOLE_RUN_PEAK' and s['actual_controller_live'] is False,'finished correctly qualified sampler')
 result=dict(status='FULL_SCALAR_MATHEMATICS_KERNEL_CLOSED_PRIME_COUNTS_AND_C_PV_SEPARATE',rows=d['rows'],stop=d['stop'],kernel_units=len(rows),result_sha256=sha(a.result),controller_sha256=d['controller_sha256'],wall_seconds=d['seconds'],selected_cpu_seconds=sum(x['cpu_seconds'] for x in rows),largest_actual_worker_rss_bytes=max(x['peak_rss_bytes'] for x in rows),sampled_aggregate_rss_bytes=s['sampled_peak_summed_lean_RSS_bytes'],sampled_scoped_logical_disk_bytes=s['sampled_peak_scoped_logical_disk_bytes'],includes_before_monitor_start=False,actual_failed_workers=0,actual_worker_oom_kills_observed=0,all_raw_values_and_pivots_joined_to_original_binary=True,prime_counts_proved=False,source_first_PV=False,mathematical_statement='FullFiniteScalars.ScalarCertificate38358837683 1490000000001 FullAdaptiveScalars.allRows: exact half-open coverage, every strict integer predicate and every actual real e/log enclosure; NO CountsCorrect claim.',final_axioms=d['records'][-1]['axioms'],independent_validation=verified,compilations=rows,summary_source_sha256=sha(__file__))
 a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','rows','kernel_units','wall_seconds','selected_cpu_seconds','largest_actual_worker_rss_bytes','sampled_aggregate_rss_bytes','sampled_scoped_logical_disk_bytes']}))
if __name__=='__main__':main()
