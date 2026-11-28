#!/usr/bin/env python3
"""Deterministic native corroboration/mutation controls for the initialize_root source contract.
This is a supplementary execution test, not a proof or a complete ANT PV claim.
"""
from __future__ import annotations
import argparse,hashlib,json,os,random,re,shutil,subprocess,sys,time
from pathlib import Path

def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,value):
    need(not p.exists(),'fresh receipt required')
    t=p.with_name('.'+p.name+'.tmp')
    with t.open('x') as f:
        json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def root(n):
    u=10**36;pi=3141592653589793238462643383279502884
    x=2*pi//n;x2=x*x//u;ct=u;st=x;cr=u;sr=x
    for i in range(1,11):
        ct=(ct*x2//u)//(2*i*(2*i-1));st=(st*x2//u)//(2*i*(2*i+1))
        cr+=(-1 if i%2 else 1)*ct;sr+=(-1 if i%2 else 1)*st
    return cr,-sr
def encode(z):
    n=abs(z);digits=[]
    for _ in range(5):digits.append(n%10**9);n//=10**9
    need(n==0,'root model exceeds source limb capacity')
    return digits+[int(z<0)]
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',required=True,type=Path);ap.add_argument('--cc',default='cc');a=ap.parse_args()
    need(not a.out.exists(),'fresh owned output directory required');a.out.mkdir(parents=True)
    began=time.monotonic();pv=Path(__file__).resolve().parent.parent/'pv';compiler=shutil.which(a.cc);need(compiler is not None,'C compiler missing')
    seed=0x080B007;rng=random.Random(seed);cases=[];statements=[];expected=[]
    for n in [131072,16777216]:
      for work,start in [(0,128),(64,0),(400,16),(1,100)]:
        for repeat in range(2):
          old=[rng.randrange(2**64) for _ in range(512)];model=encode(root(n)[0])+encode(root(n)[1]);cases.append(dict(n=n,work=work,root=start,repeat=repeat))
          # Root words and every physical word outside both writable slices are
          # checked against an independent Python integer model and old input.
          checks=''.join('if(aa['+str(start+k)+']!='+str(v)+'ULL)return '+str(k+2)+';' for k,v in enumerate(model))
          checks+=''.join('if(aa['+str(k)+']!='+str(v)+'ULL)return 40;' for k,v in enumerate(old) if not(work<=k<work+80 or start<=k<start+12))
          statements.append('{uint64_t aa[512]={'+','.join(str(v)+'ULL' for v in old)+'};uint64_t s=initialize_root(aa+'+str(start)+','+str(n)+'ULL,aa+'+str(work)+');if(s!=0ULL)return 1;'+checks+'puts("OK");}')
          expected.append('OK\n')
    mutations=[('pi-high-limb','work[4ULL]=3ULL;','work[4ULL]=2ULL;'),('root-divisor','divide_small(work,5ULL,n,0ULL);','divide_small(work,5ULL,(n*2ULL),0ULL);'),('imaginary-sign','root[11ULL]=1ULL;canonical_sign','root[11ULL]=0ULL;canonical_sign'),('cosine-initialization','work[16ULL]=1ULL;','work[16ULL]=2ULL;')]
    rows=[]
    for formal,concrete in [('FFTSource.lean','w4_fft.c'),('FapFFTSource.lean','fap_fft.c'),('FFTRecursiveSource.lean','w4_fft_recursive.c'),('FapFFTRecursiveSource.lean','fap_fft_recursive.c')]:
      source=pv/'fft'/concrete;lean=pv/'lean'/formal;text=lean.read_text();match=re.search(r'^def sourceChars[^\n]*\[(.*?)\]\s*$',text,re.M);need(match is not None,'missing formal source characters')
      chunks=match.group(1).split(', ');need(all(re.fullmatch(r'Char\.ofNat \d+',x) for x in chunks),'unsupported formal source character encoding')
      encoded=''.join(chr(int(x[11:])) for x in chunks).encode();need(encoded==source.read_bytes(),'concrete source/formal source differ')
      snapshot=a.out/concrete;snapshot.write_bytes(encoded);harness=a.out/(concrete+'.test.c')
      prefix='#include <stdint.h>\n#include <limits.h>\n_Static_assert(CHAR_BIT==8 && sizeof(uint64_t)==8 && sizeof(void*)==8,"selected ABI");\n#define main saved_numerical_main\n#include '+json.dumps(concrete)+'\n#undef main\nint main(void){\n'
      harness.write_text(prefix+'\n'.join(statements)+'\nreturn 0;}\n');exe=a.out/(concrete+'.test')
      cmd=[compiler,'-std=c11','-O2',str(harness),'-o',str(exe)];built=subprocess.run(cmd,capture_output=True,text=True);need(built.returncode==0,'native baseline compilation failed: '+built.stderr)
      run=subprocess.run([str(exe)],capture_output=True,text=True);need(run.returncode==0 and run.stdout==''.join(expected) and run.stderr=='','native baseline/model/slice mismatch')
      mutation_rows=[]
      for name,old,new in mutations:
        need(encoded.decode().count(old)==1,'mutation must target exactly one source fragment: '+name)
        mutant=a.out/(concrete+'.'+name+'.c');mutant.write_text(encoded.decode().replace(old,new));mh=a.out/(concrete+'.'+name+'.test.c');mh.write_text(harness.read_text().replace(json.dumps(concrete),json.dumps(mutant.name)))
        me=a.out/(concrete+'.'+name+'.test');mc=[compiler,'-std=c11','-O2',str(mh),'-o',str(me)];b=subprocess.run(mc,capture_output=True,text=True);need(b.returncode==0,'mutation did not compile: '+name)
        r=subprocess.run([str(me)],capture_output=True,text=True);need(r.returncode>0,'wrong-source mutation must fail model/slice check normally: '+name)
        mutation_rows.append(dict(name=name,original_fragment=old,mutated_fragment=new,source_sha256=sha(mutant),harness_sha256=sha(mh),command=mc,exitcode=r.returncode,stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),stderr_sha256=hashlib.sha256(r.stderr.encode()).hexdigest()))
      rows.append(dict(formal_source=str(lean),formal_sha256=sha(lean),concrete_source=str(source),source_sha256=sha(source),snapshot=str(snapshot),command=cmd,harness_sha256=sha(harness),executable_sha256=sha(exe),output_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),cases=len(cases),mutations=mutation_rows))
    atomic(a.out/'RESULT.json',dict(status='PASS_NATIVE_ROOT_CORROBORATION_AND_WRONG_SOURCE_CONTROLS_ONLY',source_first_PV_complete=False,proof=False,seed=seed,cases=cases,rows=rows,script_sha256=sha(Path(__file__)),python=sys.version,python_optimization=sys.flags.optimize,compiler=str(compiler),compiler_sha256=sha(Path(compiler)),compiler_version=subprocess.run([compiler,'--version'],check=True,capture_output=True,text=True).stdout,seconds=time.monotonic()-began))
    print('PASS native initializer corroboration: 16 cases and four wrong-source controls per original source; supplementary tests only')
if __name__=='__main__':main()
