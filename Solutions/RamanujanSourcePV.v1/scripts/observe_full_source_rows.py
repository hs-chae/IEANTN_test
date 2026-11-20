#!/usr/bin/env python3
"""Ordinary native observation of ALL original scalar rows; not caller PV.
Outputs are streamed into a digest; no large output arrays are saved.
"""
from pathlib import Path
import argparse,hashlib,json,os,platform,resource,shutil,struct,subprocess,time
from execute_full_scalar_certificate import need,read,sha
S=Path(__file__).resolve().parents[1]
DRIVER=r'''#include <stdint.h>
#include <stdio.h>
#include <limits.h>
#include "verified_finite_cell.c"
_Static_assert(CHAR_BIT==8 && sizeof(uint64_t)==8, "specified input ABI");
int main(int argc,char **argv) {
  uint64_t header[2]={rpc_e_low(),rpc_e_high()};
  if(argc!=65 || fwrite(header,8,2,stdout)!=2) return 2;
  uint64_t total=0;
  for(int file=1;file<argc;++file) {
    FILE *input=fopen(argv[file],"rb"); if(!input) return 3;
    uint64_t row[7]; size_t got;
    while((got=fread(row,8,7,input))!=0) {
      if(got!=7 || rpc_finite_cell(row[0],row[1],row[2],row[3],row[4],row[5],row[6])!=1) {
        fprintf(stderr,"scalar failure at record %llu\n",(unsigned long long)total); return 4;
      }
      uint64_t logarithm=rpc_log_upper(row[0]);
      if(fwrite(&logarithm,8,1,stdout)!=1) return 5;
      ++total;
    }
    if(ferror(input) || fclose(input)!=0) return 6;
  }
  if(total!=1755663 || fflush(stdout)!=0) return 7;
  fprintf(stderr,"processed=%llu\n",(unsigned long long)total);
  return 0;
}
'''
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--original-manifest',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--cpu',type=int,required=True);a=p.parse_args();m=read(a.original_manifest);context=read(a.context)
 need(m['rows']==1755663 and m['full_locked_prefix']is True and m['prime_counts_formally_proved_here']is False,'exact original full scalar scope');need(platform.machine()in ['x86_64','amd64']and __import__('sys').byteorder=='little','specified little-endian64-bit native observation');out=a.out.resolve();need(not out.exists()and out.is_relative_to(Path(context['new_application_object_root']).resolve().parent),'fresh owned native observation');need(a.cpu in os.sched_getaffinity(0),'actual available CPU')
 paths=[Path(x['path'])for x in m['native_binary_inputs']];need(len(paths)==64,'all64 fixed original files');expected=hashlib.sha256();expected.update(struct.pack('<QQ',3133965575612453533,3133965575612453555));rows=0
 for source,pin in zip(paths,m['native_binary_inputs']):
  need(sha(source)==pin['sha256'],'exact original binary identity')
  with source.open('rb')as f:
   for raw in iter(lambda:f.read(56*4096),b''):
    need(len(raw)%56==0,'whole seven-word records')
    for row in struct.iter_unpack('<7Q',raw):expected.update(struct.pack('<Q',row[5]));rows+=1
 need(rows==1755663,'every exact original row');out.mkdir(parents=True);source_pins={}
 for name in ['verified_finite_cell.c','verified_finite_exp.c','verified_finite_log.c']:
  original=S/'c'/name;payload=original.read_bytes();source_pins[str(original)]=hashlib.sha256(payload).hexdigest();(out/name).write_bytes(payload)
 driver=out/'observe_all_rows.c';driver.write_text(DRIVER)
 def limits():os.sched_setaffinity(0,{a.cpu});resource.setrlimit(resource.RLIMIT_AS,(24*1024**3,24*1024**3))
 cc=Path(shutil.which('gcc')or'');need(cc.is_file(),'actual GCC compiler');cc=cc.resolve();exe=out/'observe_all_rows';command=[str(cc),'-O2','-std=c11','-Wall','-Wextra','-Werror','-Wno-error=empty-body','-I',str(out),str(driver),'-o',str(exe)];started=time.monotonic();compiled=subprocess.run(command,capture_output=True,text=True,preexec_fn=limits);(out/'compile.stdout').write_text(compiled.stdout);(out/'compile.stderr').write_text(compiled.stderr);need(compiled.returncode==0,'actual source compilation')
 h=hashlib.sha256();size=0;run_command=['/usr/bin/time','-v','-o',str(out/'rusage.txt'),str(exe),*map(str,paths)];t=time.monotonic()
 with(out/'stderr').open('wb')as stderr:
  child=subprocess.Popen(run_command,stdout=subprocess.PIPE,stderr=stderr,preexec_fn=limits)
  for block in iter(lambda:child.stdout.read(1048576),b''):h.update(block);size+=len(block)
  returncode=child.wait()
 need(returncode==0 and size==16+8*1755663 and h.hexdigest()==expected.hexdigest(),'complete actual C output agrees with every original scalar row')
 for path,pin in source_pins.items():need(sha(path)==pin==sha(out/Path(path).name),'unchanged original/snapshotted source association')
 result=dict(status='ORDINARY_NATIVE_ALL_C_SCALAR_OUTPUTS_OBSERVED_NOT_CALLER_PV_OR_PRIME_COUNT_PROOF',rows=rows,output_bytes=size,output_sha256=h.hexdigest(),expected_sha256=expected.hexdigest(),execution_seconds=time.monotonic()-t,total_seconds=time.monotonic()-started,source_pins=source_pins,driver=str(driver),driver_sha256=sha(driver),compiler=str(cc),compiler_sha256=sha(cc),compiler_version=subprocess.check_output([str(cc),'--version'],text=True),compile_command=command,execution_command=run_command,executable_sha256=sha(exe),original_manifest_sha256=sha(a.original_manifest),prime_counts_formally_proved_here=False,caller_source_PV=False,rusage_sha256=sha(out/'rusage.txt'),cpu=a.cpu,output_data_retained=False)
 pending=out/'RESULT.pending';pending.write_text(json.dumps(result,indent=2)+'\n');pending.replace(out/'RESULT.json');print(json.dumps({k:result[k]for k in ['status','rows','output_bytes','output_sha256','execution_seconds']}))
if __name__=='__main__':main()
