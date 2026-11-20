#!/usr/bin/env python3
"""Ordinary native observations from the accepted packed masks, not source PV.
The caller/loading/build/runtime observations remain unverified. Mathematical
source execution is established separately by the Lean selected consumer.
"""
from pathlib import Path
import argparse, hashlib, json, math, os, re, shutil, struct, subprocess, sys, time
from benchmark_segment_checker import need, sha, strict_json
S = Path(__file__).resolve().parents[1]
ACCEPTED_MASK_SHA = {'P':'2f6b880edf1b009758ccd4cac49644c299b02df3cfe52731e98c414dacc5775e',
 'Q':'6c18a97a8d791deb7b915419d165d2d88911b19c72e70db74f5805b618f9344d'}
DRIVER = r'''#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
extern uint64_t rpc_check_segment(uint64_t,uint64_t,uint64_t,uint64_t*,uint64_t*);
int main(int argc,char **argv){
 if(argc!=3)return 2;
 uint64_t lo=strtoull(argv[1],0,10),length=strtoull(argv[2],0,10);
 if(lo<2||length==0||length>1500000||lo+length-1>2000000000000ULL)return 3;
 uint64_t *claims=malloc(length*sizeof(uint64_t)),*flags=malloc(length*sizeof(uint64_t));
 if(!claims||!flags)return 4;
 if(fread(claims,sizeof(uint64_t),length,stdin)!=length)return 5;
 uint64_t result=rpc_check_segment(lo,lo+length-1,length,claims,flags);
 claims[length/2]^=1;
 uint64_t bad=rpc_check_segment(lo,lo+length-1,length,claims,flags);
 claims[length/2]^=1;
 uint64_t cap=rpc_check_segment(lo,lo+length-1,length-1,claims,flags);
 printf("{\"lo\":%llu,\"length\":%llu,\"result\":%llu,\"mutated_result\":%llu,\"short_capacity_result\":%llu}\n",(unsigned long long)lo,(unsigned long long)length,(unsigned long long)result,(unsigned long long)bad,(unsigned long long)cap);
 free(claims);free(flags);return 0;
}
'''
def main():
 p=argparse.ArgumentParser(allow_abbrev=False)
 p.add_argument('--p-source',type=Path,required=True);p.add_argument('--q-source',type=Path,required=True)
 p.add_argument('--out',type=Path,required=True);p.add_argument('--cpu',type=int,default=32)
 a=p.parse_args();out=a.out.resolve()
 need(not out.exists(),'fresh owned observation output required')
 need(sys.byteorder=='little','explicit little-endian uint64 input ABI')
 need(a.cpu in os.sched_getaffinity(0),'actual CPU availability')
 out.mkdir(parents=True);caller=out/'caller.c';caller.write_text(DRIVER)
 cc=Path(shutil.which('cc')).resolve();executable=out/'check-packed-segment'
 command=[str(cc),'-std=c11','-O3',str(S/'c/verified_segment_checker.c'),str(caller),'-o',str(executable)]
 c=subprocess.run(command,capture_output=True,check=False)
 (out/'compile.stdout').write_bytes(c.stdout);(out/'compile.stderr').write_bytes(c.stderr)
 need(c.returncode==0,'unchanged C checker/caller compilation failed')
 records=[]
 for tag,source,lo,width,expected in [('P',a.p_source,38358837684,1000000,40917),('Q',a.q_source,14111427771,367880,15973)]:
  need(sha(source)==ACCEPTED_MASK_SHA[tag],'exact accepted kernel-mask source bytes required')
  text=source.read_text();match=re.search(r'def bits : Nat := (0x[0-9a-f]+)',text)
  need(match is not None,'exact accepted bitmask literal missing')
  need(f'primeBits {lo} {width} = bits' in text,'exact mathematical query mismatch')
  bits=int(match.group(1),16);need(bits.bit_length()<=width,'out-of-window set bit')
  data=bytearray(8*width)
  for i in range(width):
   struct.pack_into('<Q',data,8*i,(bits>>i)&1)
  case=out/tag;case.mkdir();run_command=['/usr/bin/time','-v','-o',str(case/'rusage.txt'),'/usr/bin/prlimit','--as='+str(24<<30),'--','/usr/bin/taskset','-c',str(a.cpu),str(executable),str(lo),str(width)]
  start=time.monotonic();r=subprocess.run(run_command,input=data,capture_output=True,check=False)
  elapsed=time.monotonic()-start;(case/'stdout').write_bytes(r.stdout);(case/'stderr').write_bytes(r.stderr)
  need(r.returncode==0,'native run failed; partial evidence retained')
  result=strict_json(r.stdout.decode('ascii'))
  for key in ['lo','length','result','mutated_result','short_capacity_result']:
   need(type(result[key]) is int and result[key]>=0,'strict output integer '+key)
  need(result==dict(lo=lo,length=width,result=expected,mutated_result=0,short_capacity_result=0),'native expected output or negative control failed')
  peak=re.search(r'Maximum resident set size \(kbytes\): (\d+)',(case/'rusage.txt').read_text());need(peak is not None,'missing measured RSS')
  result.update(command=run_command,elapsed_seconds=elapsed,peak_rss_bytes=int(peak.group(1))*1024,
    input_uint64_bytes=len(data),input_sha256=hashlib.sha256(data).hexdigest(),accepted_mask_source=str(source.resolve()),accepted_mask_source_sha256=sha(source),
    stdout_sha256=sha(case/'stdout'),stderr_sha256=sha(case/'stderr'),rusage_sha256=sha(case/'rusage.txt'))
  (case/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');records.append(result)
 receipt=dict(status='ORDINARY_NATIVE_ACCEPTED_MASK_C_CHECKER_OBSERVATIONS_PASS_NOT_PV',source_first_PV_established_by_this_receipt=False,
  boundary='Unverified caller/input loading/compiler/runtime/hardware observations only; actual Lean C-source execution and mathematical consumers are separate accepted proofs.',
  c_source=str(S/'c/verified_segment_checker.c'),c_source_sha256=sha(S/'c/verified_segment_checker.c'),c_source_bytes=(S/'c/verified_segment_checker.c').stat().st_size,
  caller_source_sha256=sha(caller),compiler=str(cc),compiler_sha256=sha(cc),compiler_version=subprocess.check_output([str(cc),'--version'],text=True),
  binary_sha256=sha(executable),script_sha256=sha(Path(__file__)),imported_observer_sha256=sha(S/'scripts/benchmark_segment_checker.py'),build_command=command,random_seed=None,
  large_input_files_saved=False,records=records)
 (out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(dict(status=receipt['status'],outputs=[x['result']for x in records])))
if __name__=='__main__':main()
