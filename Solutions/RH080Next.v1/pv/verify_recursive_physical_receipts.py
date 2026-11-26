#!/usr/bin/env python3
"""Validate all24 retained compiled observations. This is not a semantic proof."""
import argparse,hashlib,json,math,os,re
from pathlib import Path
CONTROLLER_SHA="6692cb0ba165c83623a6f7781cd6871f7e8376985bfe25ee06cd79a35891b9f5"
COMPILER_SHA='821af3c74506283c179ca413bb33e6b528805a4dd8a5c09df125e5ad560a9e89'
COMPILER_VERSION='x86_64-linux-gnu-gcc-11 (Ubuntu 11.4.0-1ubuntu1~22.04.3) 11.4.0'
TARGETS={"fap":("fap_fft_recursive.c",131072,"781796015790084776\n","c1b958953998c2b655a40b3e25689a33c28d36ab2d145fdb22547a47ff5aa558"),"w4":("w4_fft_recursive.c",16777216,"7813568381279800\n","0c9e29db9bbfacd8ed049dc8e4b2a2f18d8ae146c1d0e4dd47a93cd89b80e22b")}
MODES={"O0":["-O0"],"O2":["-O2"],"O3":["-O3"],"ubsan":["-O1","-fsanitize=undefined","-fno-sanitize-recover=all"]}
RUNS={"recursive-physical-final-v1":0,"recursive-physical-final-O-v1":1,"recursive-physical-final-OO-v1":2}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict(p):
    def pairs(items):
        d={}
        for k,v in items:
            need(k not in d,"duplicate JSON key "+k);d[k]=v
        return d
    def bad(v):raise ValueError("nonfinite JSON "+v)
    return json.loads(p.read_text(encoding="utf-8"),object_pairs_hook=pairs,parse_constant=bad)
def number(x):return type(x)in[int,float]and math.isfinite(x)and x>0
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--runs-root',required=True,type=Path);ap.add_argument('--source-root',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args();need(not a.output.exists(),"fresh acceptance receipt required")
    need(sha(a.source_root/'reproduce_recursive_physical.py')==CONTROLLER_SHA,"reviewed physical controller changed")
    verified=[];banks=[];binaryGroups={}
    for run,opt in RUNS.items():
        b=a.runs_root/run;p=strict(b/'PLAN.json');result=strict(b/'RESULT.json')
        need(p['status']=='PHYSICAL_SOURCE_OBSERVATION_PLAN_NOT_PROOF',"wrong physical plan")
        need(p['python_optimize']==opt and type(p['python_optimize'])is int,"wrong Python optimization population")
        need(p['source_first_PV_complete']is False and p['kernel_certificate_complete']is False,"physical plan mislabeled as proof")
        need(p['controller_sha256']==CONTROLLER_SHA==sha(b/'executed_controller.py'),"executed controller identity")
        compiler=Path(p['compiler']);need(compiler.is_absolute()and compiler.is_file()and sha(compiler)==p['compiler_sha256']==COMPILER_SHA,"compiler identity")
        need(p['compiler_version']==COMPILER_VERSION,"pinned compiler version")
        need(p['modes']==MODES and list(p['modes'])==list(MODES),"compiler-mode universe or order")
        need([x['program']for x in p['source_rows']]==list(TARGETS),"source universe or order")
        cap=p['memory_cap_bytes'];need(type(cap)is int and cap%2**30==0 and 2**30<=cap<=300*2**30,"invalid memory allowance")
        need(type(p['available_ram_bytes'])is int and p['available_ram_bytes']>=cap+256*2**30,"recorded reserve prerequisite")
        if cap>64*2**30:need(p['available_ram_bytes']>=2**40,"recorded high-memory prerequisite")
        for row in p['source_rows']:
            name=row['program'];filename,grid,expected,digest=TARGETS[name]
            need(Path(row['source']).name==filename and row['grid']==grid and row['locked_output']==expected and row['source_sha256']==digest,"source plan identity "+name)
            need(sha(a.source_root/'fft'/filename)==digest==sha(b/filename),"preserved source/snapshot bytes "+name)
        need(result['status']=='PASS_PHYSICAL_SOURCE_OBSERVATIONS_NOT_ALONE_PV'and result['source_first_PV_complete']is False and result['numerical_assumptions_discharged_by_this_script']is False,"physical result mislabeled as proof")
        need(result['plan_sha256']==sha(b/'PLAN.json'),"physical plan receipt association")
        pairs=[(x['program'],x['mode'])for x in result['runs']];expectedPairs=[(name,mode)for name in TARGETS for mode in MODES]
        need(pairs==expectedPairs and len(set(pairs))==8,"missing/duplicate/extra run route")
        need({x.name for x in b.glob('*.RECEIPT.json')}=={name+'-'+mode+'.RECEIPT.json'for name,mode in expectedPairs},"receipt file population")
        for recorded in result['runs']:
            name=recorded['program'];mode=recorded['mode'];stem=name+'-'+mode;row=strict(b/(stem+'.RECEIPT.json'));need(row==recorded,"aggregate/per-run receipt mismatch "+stem)
            filename,grid,expected,digest=TARGETS[name];command=row['compile_command'];need(type(command)is list and len(command)>=3,"invalid compile command")
            logical=Path(command[-1]).parent;need(logical.is_absolute()and logical.name==run,"compile run identity "+stem)
            need(command==[str(compiler),'-std=c11','-Wall','-Wextra','-Werror','-pedantic',*MODES[mode],str(logical/filename),'-o',str(logical/(stem+'.bin'))],"compile flags/source/output association "+stem)
            execute=['/usr/bin/time','-v','-o',str(logical/(stem+'.time')),'prlimit','--as='+str(cap),'--stack='+str(256*2**20),'--',str(logical/(stem+'.bin'))]
            need(row['execute_command']==execute,"execution/binary/resource association "+stem)
            need(not(b/(stem+'.compile.stdout')).read_bytes()and not(b/(stem+'.compile.stderr')).read_bytes(),"compile diagnostics "+stem)
            need(row['source_sha256']==digest and row['executable_sha256']==sha(b/(stem+'.bin')),"run source/executable identity "+stem)
            stdout=(b/(stem+'.stdout')).read_bytes();stderr=(b/(stem+'.stderr')).read_bytes();resource=(b/(stem+'.time')).read_text()
            need(sha(b/(stem+'.stdout'))==row['stdout_sha256']and sha(b/(stem+'.stderr'))==row['stderr_sha256']and sha(b/(stem+'.time'))==row['time_sha256'],"log/time identity "+stem)
            need(stdout==expected.encode('ascii')and re.fullmatch(rb'[0-9]+\n',stdout)is not None and row['output']==expected,"exact decimal-LF output "+stem)
            need(not stderr and type(row['returncode'])is int and row['returncode']==0 and row['acceptance']is True,"failed/diagnostic native execution "+stem)
            rss=re.findall(r'^\s*Maximum resident set size \(kbytes\):\s*(\d+)\s*$',resource,re.M);exits=re.findall(r'^\s*Exit status:\s*(-?\d+)\s*$',resource,re.M)
            need(len(rss)==1 and len(exits)==1 and exits[0]=='0'and 'Command terminated by signal'not in resource,"resource process completion "+stem)
            need(type(row['peak_rss_kib'])is int and row['peak_rss_kib']==int(rss[0])and 0<row['peak_rss_kib']<=cap//1024,"actual peak RSS association "+stem)
            need(number(row['compile_seconds'])and number(row['execution_seconds']),"invalid elapsed time "+stem)
            need(row['oom_event']=='not_inferred_from_exit_code; inspect enclosing cgroup memory.events',"unjustified OOM assertion "+stem)
            binaryGroups.setdefault(name+'/'+mode,[]).append(row['executable_sha256'])
            verified.append(dict(run=run,python_optimize=opt,program=name,mode=mode,output=expected,receipt_sha256=sha(b/(stem+'.RECEIPT.json')),executable_sha256=row['executable_sha256'],source_sha256=digest,stdout_sha256=row['stdout_sha256'],stderr_sha256=row['stderr_sha256'],time_sha256=row['time_sha256'],execution_seconds=row['execution_seconds'],peak_rss_kib=row['peak_rss_kib'],oom_counter='NOT_RETAINED_NOT_INFERRED'))
        need(number(result['seconds']),"invalid total elapsed time")
        actualDisk=sum(x.stat().st_size for x in b.rglob('*')if x.is_file()and x.name!='RESULT.json');need(result['disk_bytes']==actualDisk,"recorded artifact footprint association")
        banks.append(dict(run=run,plan_sha256=sha(b/'PLAN.json'),result_sha256=sha(b/'RESULT.json'),compiler_sha256=p['compiler_sha256']))
    need(len(verified)==24,"wrong total physical population")
    result=dict(status='PASS_24_RETAINED_PHYSICAL_OBSERVATIONS_NOT_SEMANTIC_PROOF',runs=verified,banks=banks,controller_sha256=CONTROLLER_SHA,validator_sha256=sha(Path(__file__)),source_first_PV_complete=False,mathematical_assumptions_discharged_by_validator=False,oom_counter_status='No retained completed cgroup memory.events receipts; do not infer counter0.',binary_groups=binaryGroups,scope='Exact24 existing physical observations, both unchanged C profiles,4 compiler modes under3 Python optimizer modes. Does not rerun24 workloads or authenticate history independently of trusted execution/receipt recording.',UBSan_hash_note='UBSan may embed absolute source paths, so different run-directory binary hashes are retained rather than rejected.',trust=['precise selected C compiler/core runtime/stdio/OS/hardware contracts','trusted association of compile/execution commands and retained artifact receipts to actual subprocess execution'])
    temp=a.output.with_name('.'+a.output.name+'.tmp')
    with temp.open('x')as f:json.dump(result,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(temp,a.output)
    finally:temp.unlink()
    print(json.dumps(dict(status=result['status'],runs=24,max_peak_rss_kib=max(x['peak_rss_kib']for x in verified),receipt=str(a.output),sha256=sha(a.output))))
if __name__=='__main__':main()
