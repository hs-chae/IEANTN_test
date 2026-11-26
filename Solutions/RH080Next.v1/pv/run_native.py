#!/usr/bin/env python3
"""Reproduce source-compiled numerical outputs; this receipt alone is not PV."""
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
EXPECTED={'fap_scalars':'799999999999990000\n16297236881532502\n1142770022680000\n14047086942420000\n40617111385600000\n760944122290429\n6915614327570000\n','flat_population_norm':'1120475208606944546\n','window_scalars':'3599999999999999998\n73712934591273687\n1146154494119977\n14033179036371096\n40713308729275680\n69452659995205718\n6911696218056550\n','population_norm':'887721072633027910\n'}
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):
    need(not p.exists(),'Fresh receipt required');tmp=p.with_name('.'+p.name+'.tmp')
    with tmp.open('x')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(tmp,p)
    finally:tmp.unlink()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--program',choices=['all',*EXPECTED],default='all');ap.add_argument('--cc',default='gcc');a=ap.parse_args()
    need(not a.run.exists(),'Fresh native run directory required');a.run.mkdir(parents=True)
    cc=Path(shutil.which(a.cc)or a.cc).resolve();need(cc.is_file(),'C compiler unavailable')
    programs=list(EXPECTED)if a.program=='all'else[a.program];rows=[]
    for name in programs:
        origin=HERE/(name+'.c');source=a.run/(name+'.c');source.write_bytes(origin.read_bytes())
        for mode,flags in [('O0',['-O0']),('O2',['-O2']),('O3',['-O3']),('ubsan',['-O1','-fsanitize=undefined','-fno-sanitize-recover=all'])]:
            binary=a.run/(name+'_'+mode);command=[str(cc),'-std=c11','-Wall','-Wextra','-Werror','-pedantic',*flags,str(source),'-o',str(binary)]
            start=time.monotonic();compiled=subprocess.run(command,capture_output=True);need(compiled.returncode==0,'C compile failed: '+compiled.stderr.decode(errors='replace'))
            timing=a.run/(name+'_'+mode+'.time');executed=subprocess.run(['/usr/bin/time','-v','-o',str(timing),str(binary)],capture_output=True)
            need(executed.returncode==0,'Native execution failed; returncode '+str(executed.returncode))
            need(not executed.stderr,'Unexpected stderr/UBSan report')
            stdout=executed.stdout.decode('ascii');need(re.fullmatch(r'(?:[0-9]+\n)+',stdout)is not None,'Malformed decimal output')
            need(stdout==EXPECTED[name],'Source output differs from recorded Lean-proved result')
            resource=timing.read_text();rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',resource)
            need(rss is not None,'Missing actual peak-RAM receipt')
            rows.append(dict(program=name,mode=mode,command=command,source_sha256=sha(source),executable_sha256=sha(binary),stdout=stdout,returncode=executed.returncode,seconds=time.monotonic()-start,peak_rss_kib=int(rss.group(1)),resource_receipt_sha256=sha(timing),oom=False))
        need(sha(origin)==sha(source),'Source changed during native reproduction')
    negative=[]
    if 'population_norm'in programs:
        for p in sorted((HERE/'negative').glob('*.c')):
            source=a.run/p.name;source.write_bytes(p.read_bytes());binary=a.run/p.stem
            command=[str(cc),'-std=c11','-Wall','-Wextra','-Werror','-O2',str(source),'-o',str(binary)]
            compiled=subprocess.run(command,capture_output=True);need(compiled.returncode==0,'Mutation did not compile')
            executed=subprocess.run([str(binary)],capture_output=True);need(executed.returncode==0,'Mutation crashed')
            need(executed.stdout.decode('ascii')!=EXPECTED['population_norm'],'Mutation kept original numerical output; choose a useful test')
            negative.append(dict(name=p.stem,source_sha256=sha(source),executable_sha256=sha(binary),stdout=executed.stdout.decode('ascii'),stale_output_rejected=True))
    result=dict(status='PASS_ACTUAL_COMPILED_SOURCE_OBSERVATIONS_NOT_ALONE_PV',compiler=str(cc),compiler_sha256=sha(cc),compiler_version=subprocess.check_output([str(cc),'--version'],text=True).splitlines()[0],controller_sha256=sha(Path(__file__)),python_version=subprocess.check_output(['python3','--version'],text=True).strip(),python_optimize=sys.flags.optimize,runs=rows,negative_mutations=negative,disk_bytes=sum(p.stat().st_size for p in a.run.rglob('*')if p.is_file()))
    save(a.run/'RESULT.json',result);print(json.dumps(dict(status=result['status'],runs=len(rows),mutations=len(negative))))
if __name__=='__main__':main()
