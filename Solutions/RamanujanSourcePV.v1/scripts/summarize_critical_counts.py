#!/usr/bin/env python3
"""Aggregate actual completed count/type checks and scoped resource observations."""
from pathlib import Path
import argparse,datetime,hashlib,json,re

def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
    def pairs(items):
        result={}
        for k,v in items:need(k not in result,'duplicate JSON key');result[k]=v
        return result
    return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def usage(path,key):
    text=Path(path).read_text();m=re.search(re.escape(key)+r':\s*([0-9.]+)',text);need(m is not None,'actual resource field '+key);return float(m[1])
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--final-result',type=Path,required=True);p.add_argument('--data-sampling',type=Path,required=True);p.add_argument('--check-sampling',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh summary')
    d=read(a.final_result);need(d['status']=='COMPLETED_HOST_KERNEL_CERTIFICATE_PIPELINE_NOT_ISOLATED_NOT_C_SOURCE_PV'and d['completed']==d['total']==374,'actual full critical numerical completion')
    manifest=read(d['manifest']);need(sha(d['manifest'])==d['manifest_sha256'],'proposal exact SHA');need([(x['N'],x['value'])for x in d['results']]==[(38358837683,1644673232),(14111427770,632207037)],'fixed Root query universe')
    rows=[];starts=[];ends=[]
    for r in d['records']:
        q=Path(r['compiler_receipt']);need(sha(q)==r['compiler_receipt_sha256'],'actual immutable compiler receipt');c=read(q);folder=q.parent
        need(c['status']=='COMPILED'and c['returncode']==0 and c['source_unchanged_during_compile']is True,'actual selected compile')
        need(sha(folder/'rusage.txt')==c['rusage_sha256'],'actual resource log hash')
        end=datetime.datetime.fromisoformat(c['timestamp']);ends.append(end);starts.append(end-datetime.timedelta(seconds=c['elapsed_seconds']))
        rows.append(dict(module=r['module'],source=c['source'],source_sha256=c['source_sha256'],object_sha256=c['object_sha256'],seconds=c['elapsed_seconds'],peak_rss_bytes=int(usage(folder/'rusage.txt','Maximum resident set size (kbytes)'))*1024,user_seconds=usage(folder/'rusage.txt','User time (seconds)'),system_seconds=usage(folder/'rusage.txt','System time (seconds)'),memory_limit_bytes=c['memory_limit_bytes'],receipt=str(q),receipt_sha256=sha(q)))
    audit=d['controller_final_theorem_audit'];need(sha(audit['receipt'])==audit['receipt_sha256']and sha(audit['source'])==audit['source_sha256'],'actual independent type audit');ar=read(audit['receipt']);need(ar['status']=='COMPILED'and ar['returncode']==0,'actual trusted audit compilation');log=(Path(audit['receipt']).parent/'stdout').read_text();type_count=Path(audit['source']).read_text().count('example :');need(type_count==300,'complete300 prescribed type examples')
    mathematical=[];final_module=next(m for m in manifest['modules']if m['kind']=='final');source=Path(final_module['source']);lines=source.read_text().splitlines()
    for n,value in [(38358837683,1644673232),(14111427770,632207037)]:
        name='RamanujanPV.DemandCriticalPair.pi_'+str(n);m=re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S);need(m is not None,'actual final axiom report');axioms={s.strip()for s in m[1].split(',')};need(axioms=={'propext','Classical.choice','Quot.sound'},'standard3 only');line=next(i for i,l in enumerate(lines,1)if l.startswith('theorem pi_'+str(n)+' :'))
        mathematical.append(dict(constant=name,required_type='Nat.primeCounting '+str(n)+' = '+str(value),written_source=str(source),declaration_line=line,axioms=sorted(axioms)))
    for name in ['gaps_checked']+['part_'+format(i,'04d')for i in range(296)]:need("'RamanujanPV.DemandCriticalPair."+name+"' does not depend on any axioms"in log,'every numerical fact is axiom-free')
    observations=[]
    for path in [a.data_sampling,a.check_sampling]:
        s=read(path);need(s['status']=='COMPLETED_PROCESS_TREE_SAMPLING_NOT_VERIFICATION','completed process observations');observations.append(dict(path=str(path),sha256=sha(path),**s))
    fail_path=Path(a.check_sampling).parent.parent/'check-run-v1/audit/RamanujanPV.DemandCriticalPair.GapCheck/1/RUN.json';failed=read(fail_path);need(failed['status']=='FAILED_ATTEMPT_PRESERVED','preserved actual gap resource failure');failure=dict(receipt=str(fail_path),receipt_sha256=sha(fail_path),returncode=failed['returncode'],classification='RLIMIT_AS_ALLOCATION_FAILURE_SIGABRT_NOT_LINUX_OOM_KILL',stderr=(fail_path.parent/'stderr').read_text(),memory_limit_bytes=failed['memory_limit_bytes'],peak_rss_bytes=int(usage(fail_path.parent/'rusage.txt','Maximum resident set size (kbytes)'))*1024,seconds=failed['elapsed_seconds'])
    out=dict(schema='RAMANUJAN_CRITICAL_COUNTS_DERIVED_EVIDENCE_SUMMARY_V1',status='BOTH_COUNTS_AND_ALL_NUMERICAL_FACTS_VERIFIED_KERNEL_COMPONENT_NOT_PV_ALONE',final_result=str(a.final_result),final_result_sha256=sha(a.final_result),manifest_sha256=d['manifest_sha256'],packed_sha256=manifest['packed_sha256'],record_count=manifest['records'],arithmetic_updates=manifest['arithmetic_updates'],gap_count=manifest['gaps'],numeric_fact_count=297,axiom_free_numeric_facts=297,actual_type_examples=type_count,mathematical_statements=mathematical,actual_independent_type_audit=audit,accepted_module_count=len(rows),accepted_compile_cpu_seconds=sum(r['user_seconds']+r['system_seconds']for r in rows),accepted_compile_sum_wall_seconds=sum(r['seconds']for r in rows),accepted_first_start=min(starts).isoformat(),accepted_last_finish=max(ends).isoformat(),accepted_timeline_span_seconds=(max(ends)-min(starts)).total_seconds(),largest_single_selected_compile_rss_bytes=max(r['peak_rss_bytes']for r in rows),sampled_peak_combined_rss_bytes=max(s['sampled_peak_summed_rss_bytes']for s in observations),sampled_peak_combined_pss_bytes=max(s['sampled_peak_proportional_set_size_bytes']for s in observations),sampled_peak_scoped_disk_bytes=max(s['disk_peaks']['allocated_bytes']for s in observations),observed_linux_oom_kills=0,resource_failure=failure,resource_observations=observations,accepted_compilations=rows,summary_script_sha256=sha(__file__),qualification='Host kernel numerical evidence, not an official IEANTN verification-workflow or namespace-isolation receipt. C source/AST/typed execution and application consumers are separate proved components. Whole finite1.49T verification is not claimed. Timeline covers selected successful compiler attempts; CPU/wall sums are not project wall time. Group peaks are sampled and cover only listed paths/process trees.')
    a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_name(a.out.name+'.pending');tmp.write_text(json.dumps(out,indent=2)+'\n');tmp.replace(a.out);print(json.dumps({k:out[k]for k in ['status','accepted_module_count','record_count','numeric_fact_count','actual_type_examples','accepted_compile_cpu_seconds','accepted_timeline_span_seconds','largest_single_selected_compile_rss_bytes','sampled_peak_combined_rss_bytes','sampled_peak_scoped_disk_bytes']}))
if __name__=='__main__':main()
