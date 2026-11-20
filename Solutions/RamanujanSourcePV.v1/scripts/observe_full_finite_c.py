#!/usr/bin/env python3
"""Execute unchanged actual C scalar functions on locked binary rows.
This is native supplemental observation, NOT a source-PV or prime-count proof.
The Python/ctypes input-loading caller is explicitly unverified.
"""
from pathlib import Path
import argparse,ctypes,datetime,hashlib,json,os,resource,shutil,struct,subprocess,time
S=Path(__file__).resolve().parents[1]
def need(value,message):
    if not value:raise ValueError(message)
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024**2),b''):h.update(block)
    return h.hexdigest()
def read(path):
    def pairs(items):
        d={}
        for k,v in items:
            need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite JSON')))
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--certificates',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--limit-rows',type=int,default=0);p.add_argument('--cpu',type=int,default=32);a=p.parse_args();need(a.limit_rows>=0,'nonnegative explicit profile');need(a.cpu in os.sched_getaffinity(0),'available actual CPU');os.sched_setaffinity(0,{a.cpu});need(not a.out.exists(),'fresh owned observation output');run=read(a.run);need(run['begin']==38358837683 and run['end_inclusive']==1490000000000 and run['mode']=='actual','exact original scientific workload');records=run['records'];need(len(records)==64 and len({x['chunk'] for x in records})==64,'complete fixed64 native inputs');inputs=[]
    for row in records:
        file=(a.certificates/(str(row['chunk'])+'.bin')).resolve();need(file.is_file() and not file.is_symlink(),'ordinary input file');need(file.stat().st_size==row['certificate_bytes'] and sha(file)==row['certificate_sha256'],'every original input identity');inputs.append((row,file))
    need(sum(x['certificate_bytes']//56 for x in records)==1755663,'all original full-prefix rows');a.out.mkdir(parents=True);sources={str(Path('c')/name):sha(S/'c'/name) for name in ['verified_finite_exp.c','verified_finite_log.c','verified_finite_cell.c']};compiler=Path(shutil.which('gcc')).resolve();library=a.out.resolve()/'finite-functions.so';command=[str(compiler),'-std=c11','-O3','-fPIC','-shared','-Wall','-Wextra','-Wconversion','-Werror','-Wno-empty-body',str(S/'c/verified_finite_cell.c'),'-o',str(library)];started=time.monotonic();compiled=subprocess.run(command,capture_output=True);(a.out/'compiler.stdout').write_bytes(compiled.stdout);(a.out/'compiler.stderr').write_bytes(compiled.stderr);need(compiled.returncode==0,'actual compiler failure preserved');need(all(sha(S/name)==value for name,value in sources.items()),'source changed during native compilation');lib=ctypes.CDLL(str(library));cell=lib.rpc_finite_cell;cell.argtypes=[ctypes.c_uint64]*7;cell.restype=ctypes.c_int;lo=lib.rpc_e_low;hi=lib.rpc_e_high;lo.argtypes=[];hi.argtypes=[];lo.restype=ctypes.c_uint64;hi.restype=ctypes.c_uint64;e_values=[lo(),hi()];need(e_values==[3133965575612453533,3133965575612453555],'actual C e words differ');count=0;answers=hashlib.sha256();previous=38358837683
    for row,file in inputs:
        with file.open('rb') as f:
            for data in iter(lambda:f.read(56*4096),b''):
                need(len(data)%56==0,'whole binary rows')
                for values in struct.iter_unpack('<7Q',data):
                    if a.limit_rows and count>=a.limit_rows:break
                    need(values[0]==previous and values[1]>values[0],'actual adjacency');answer=cell(*values);need(answer==1,'actual C cell rejected row '+str(count));answers.update(bytes([answer]));count+=1;previous=values[1]
                if a.limit_rows and count>=a.limit_rows:break
        if a.limit_rows and count>=a.limit_rows:break
    full=a.limit_rows==0;need(count==(1755663 if full else min(a.limit_rows,1755663)),'every requested actual C call');need(not full or previous==1490000000001,'exact full stop');need(all(sha(S/name)==value for name,value in sources.items()),'source changed during execution');result=dict(schema='RAMANUJAN_FULL_NATIVE_C_OBSERVATION_V1',status='ALL_ACTUAL_C_CALLS_RETURN_ONE_NATIVE_OBSERVATION_ONLY',timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_first_PV=False,formal_prime_count_claim=False,caller='Python/ctypes ordinary unverified input-loading caller; formal C function executions are separate',rows=count,full_locked_prefix=full,stop=previous,source_hashes=sources,input_run_sha256=sha(a.run),inputs=[dict(chunk=row['chunk'],bytes=row['certificate_bytes'],sha256=row['certificate_sha256']) for row,_ in inputs],compiler=str(compiler),compiler_sha256=sha(compiler),compiler_version=subprocess.check_output([str(compiler),'--version'],text=True),command=command,library_sha256=sha(library),e_outputs=e_values,return_bytes_sha256=answers.hexdigest(),seconds=time.monotonic()-started,self_max_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,compiler_child_max_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss*1024,cpu=a.cpu,random_seed=None,retained_disk_bytes=sum(p.stat().st_size for p in a.out.rglob('*') if p.is_file()))
    (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k in ['status','rows','full_locked_prefix','seconds','self_max_rss_bytes','compiler_child_max_rss_bytes','return_bytes_sha256','source_first_PV']}))
if __name__=='__main__':main()
