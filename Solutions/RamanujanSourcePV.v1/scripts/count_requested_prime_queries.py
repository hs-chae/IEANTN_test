#!/usr/bin/env python3
"""Census requested count arguments, not a proof of the requested values."""
from pathlib import Path
import argparse,hashlib,json,struct,time

def need(v,m):
    if not v:raise ValueError(m)
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for chunk in iter(lambda:f.read(1024**2),b''):h.update(chunk)
    return h.hexdigest()
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--certificates',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh census receipt');run=json.loads(a.run.read_text());need(run['begin']==38358837683 and run['end_inclusive']==1490000000000 and run['mode']=='actual','fixed scientific universe');started=time.monotonic();wanted={};rows=0;conflicts=0;previous=38358837683;local_rows=0
    for record in run['records']:
        file=a.certificates/(str(record['chunk'])+'.bin');need(file.stat().st_size==record['certificate_bytes'] and sha(file)==record['certificate_sha256'],'every original binary identity')
        with file.open('rb') as f:
            for data in iter(lambda:f.read(56*4096),b''):
                need(len(data)%56==0,'whole original rows')
                for n,next_n,j,P,Q,Lu,A in struct.iter_unpack('<7Q',data):
                    need(n==previous and n<next_n,'every adjacency');rows+=1;previous=next_n
                    if next_n<=38359837684:local_rows+=1
                    for argument,value in [(next_n-1,P),(j,Q)]:
                        if argument in wanted and wanted[argument]!=value:conflicts+=1
                        wanted[argument]=value
    need(rows==1755663 and previous==1490000000001,'entire original locked universe');digest=hashlib.sha256()
    for argument in sorted(wanted):digest.update(struct.pack('<QQ',argument,wanted[argument]))
    result=dict(schema='RAMANUJAN_REQUESTED_COUNT_QUERY_CENSUS_V1',status='ORDINARY_REQUESTED_ARGUMENT_CENSUS_NOT_MATHEMATICAL_COUNT_VERIFICATION',requested_rows=rows,query_sites=2*rows,unique_requested_arguments=len(wanted),duplicate_sites=2*rows-len(wanted),conflicting_requested_values=conflicts,minimum_argument=min(wanted),maximum_argument=max(wanted),sorted_argument_value_pairs_sha256=digest.hexdigest(),rows_whose_real_domain_is_inside_existing_million_theorem=local_rows,prime_count_truth_proved=False,source_execution_witnesses_constructed=False,census_author='Root; exactly every P(next-1) and Q(j) site in all64 original adaptive files; no heuristic selection',input_run_sha256=sha(a.run),script_sha256=sha(__file__),seconds=time.monotonic()-started)
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
