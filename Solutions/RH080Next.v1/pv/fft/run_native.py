#!/usr/bin/env python3
"""Reproduce actual source FFT runs. No receipt from this script is PV."""
import argparse,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
H=Path(__file__).resolve().parent
CONFIG={'w4_fft':(16777216,10**16,'7813568381279800\n'),'w4_fft_recursive':(16777216,10**16,'7813568381279800\n'),'fap_fft':(131072,10**18,'781796015790084776\n'),'fap_fft_recursive':(131072,10**18,'781796015790084776\n')}
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--program',choices=CONFIG,required=True);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--ubsan',action='store_true');ap.add_argument('--cc',default='gcc');a=ap.parse_args();need(not a.run.exists(),'Fresh run required');a.run.mkdir(parents=True)
    origin=H/(a.program+'.c');source=a.run/origin.name;source.write_bytes(origin.read_bytes());binary=a.run/a.program;cc=Path(shutil.which(a.cc)or a.cc).resolve()
    flags=['-std=c11','-Wall','-Wextra','-Werror','-O3']
    if a.ubsan:flags+=['-fsanitize=undefined','-fno-sanitize-recover=all']
    command=[str(cc),*flags,str(source),'-o',str(binary)];compiled=subprocess.run(command,capture_output=True);need(compiled.returncode==0,'Source compile failed: '+compiled.stderr.decode(errors='replace'))
    tm=a.run/'resources.time';runcommand=['/usr/bin/time','-v','-o',str(tm),str(binary)];start=time.monotonic();executed=subprocess.run(runcommand,capture_output=True);elapsed=time.monotonic()-start
    (a.run/'stdout').write_bytes(executed.stdout);(a.run/'stderr').write_bytes(executed.stderr);need(executed.returncode==0 and not executed.stderr,'Source run failed or UBSan reported')
    need(re.fullmatch(rb'[0-9]+\n',executed.stdout)is not None,'Malformed numeric stdout');grid,scale,expected=CONFIG[a.program];need(executed.stdout.decode('ascii')==expected,'Actual numeric output changed')
    need(sha(origin)==sha(source),'Source changed during run');rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tm.read_text());need(rss is not None,'No measured RSS')
    result=dict(status='PASS_ACTUAL_NATIVE_FFT_OUTPUT_OBSERVATION_NOT_PV',program=a.program,grid=grid,output_scale=scale,output_numerator=int(expected),source_sha256=sha(source),executable_sha256=sha(binary),compiler_sha256=sha(cc),compiler_version=subprocess.check_output([str(cc),'--version'],text=True).splitlines()[0],compile_command=command,execution_command=runcommand,ubsan=a.ubsan,seconds=elapsed,peak_rss_kib=int(rss.group(1)),oom=False,resources_sha256=sha(tm),source_first_FFT_PV_complete=False,mathematical_enclosure_proved_from_source=False)
    p=a.run/'RESULT.json';tmp=a.run/'.RESULT.tmp';tmp.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n');os.link(tmp,p);tmp.unlink();print(json.dumps({k:result[k]for k in ['status','program','output_numerator','seconds','peak_rss_kib']}))
if __name__=='__main__':main()
