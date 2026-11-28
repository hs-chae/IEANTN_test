#!/usr/bin/env python3
"""Actual-source quad corroboration and source-mutation controls; tests, not proof.
The original C helpers are included unchanged, and the actual main quad segment
is extracted byte-for-byte. Expected values use the pinned Lean nodal inputs and
independent Python integers. This never claims whole-main/ANT PV completion.
"""
from __future__ import annotations
import argparse,hashlib,json,os,random,re,shutil,subprocess,sys,time
from pathlib import Path

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,value):
    need(not p.exists(),'fresh receipt required');t=p.with_name('.'+p.name+'.tmp')
    with t.open('x') as f:
        json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def segment(s,fap):
    hits=list(re.finditer(r'j=0ULL;while\(j<(\d+)ULL\)\{uint64_t e=encoded_node\(j\);uint64_t value=0ULL;if',s))
    need(len(hits)==1,'actual quad loop must resolve uniquely');m=hits[0];start=m.start();i=s.index('{',m.start());depth=1;i+=1
    while depth:
        need(i<len(s),'unterminated quad body');depth+=(s[i]=='{')-(s[i]=='}');i+=1
    if fap:
        extra='status=(status+multiply_small(quad,6ULL,100ULL));';tail=s[i:];space=len(tail)-len(tail.lstrip());need(tail[space:].startswith(extra),'missing actual Fap ×100');i+=space+len(extra)
    return start,i,int(m.group(1)),s[start:i]
def words(n):
    out=[]
    for _ in range(6):out.append(n%10**9);n//=10**9
    need(n==0,'quad exceeds six-limb model');return out

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',required=True,type=Path);ap.add_argument('--cc',default='cc');a=ap.parse_args()
    need(not a.out.exists(),'fresh owned output directory required');a.out.mkdir(parents=True);began=time.monotonic();pv=Path(__file__).resolve().parent.parent/'pv';compiler=shutil.which(a.cc);need(compiler is not None,'C compiler missing')
    seed=0x080A0AD;rng=random.Random(seed);rows=[]
    for formal,concrete,fap in [('FFTSource.lean','w4_fft.c',False),('FapFFTSource.lean','fap_fft.c',True),('FFTRecursiveSource.lean','w4_fft_recursive.c',False),('FapFFTRecursiveSource.lean','fap_fft_recursive.c',True)]:
      source=pv/'fft'/concrete;lean=pv/'lean'/formal;text=lean.read_text();m=re.search(r'^def sourceChars[^\n]*\[(.*?)\]\s*$',text,re.M);need(m is not None,'missing formal source characters');chunks=m.group(1).split(', ');need(all(re.fullmatch(r'Char\.ofNat \d+',x) for x in chunks),'unsupported formal source encoding');encoded=''.join(chr(int(x[11:])) for x in chunks).encode();need(encoded==source.read_bytes(),'concrete/formal source bytes differ');original=encoded.decode();start,end,count,fragment=segment(original,fap)
      data=pv/'lean'/('FapData.lean' if fap else 'WindowData.lean');dm=re.search(r'^def encoded : List Nat := \[([0-9, ]+)\]$',data.read_text(),re.M);need(dm is not None,'missing exact nodal input');nodes=[int(x) for x in dm.group(1).split(', ')];need(len(nodes)==count==(400 if fap else 2520),'wrong locked count');need(all(0<=x<2*10**16 for x in nodes),'bad exact input');raw=sum(20*j*j*abs(e-10**16) for j,e in enumerate(nodes));expected=raw*(100 if fap else 1);digit=words(expected)
      oldcases=[[rng.randrange(2**64) for _ in range(512)] for _ in range(8)]
      for old in oldcases:old[208:214]=[0]*6
      def harness_text(include,frag):
        statements=[]
        for old in oldcases:
          checks=''.join('if(work['+str(208+k)+']!='+str(v)+'ULL)return '+str(k+2)+';' for k,v in enumerate(digit))
          checks+=''.join('if(work['+str(k)+']!='+str(v)+'ULL)return 40;' for k,v in enumerate(old) if not(160<=k<166 or 208<=k<214))
          statements.append('{uint64_t work[512]={'+','.join(str(v)+'ULL' for v in old)+'};uint64_t *temp=work+160ULL,*quad=work+208ULL;uint64_t j=0ULL,n='+str(131072 if fap else 16777216)+'ULL,status=0ULL;'+frag+'if(status!=0ULL||j!='+str(count)+'ULL)return 1;'+checks+'puts("OK");}')
        return '#include <stdint.h>\n#include <limits.h>\n_Static_assert(CHAR_BIT==8&&sizeof(uint64_t)==8&&sizeof(void*)==8,"selected ABI");\n#define main saved_numerical_main\n#include '+json.dumps(include)+'\n#undef main\nint main(void){\n'+'\n'.join(statements)+'\nreturn 0;}\n'
      snapshot=a.out/concrete;snapshot.write_bytes(encoded);harness=a.out/(concrete+'.test.c');harness.write_text(harness_text(concrete,fragment));exe=a.out/(concrete+'.test');cmd=[compiler,'-std=c11','-O2',str(harness),'-o',str(exe)];b=subprocess.run(cmd,capture_output=True,text=True);need(b.returncode==0,'native baseline compile: '+b.stderr);run=subprocess.run([str(exe)],capture_output=True,text=True);need(run.returncode==0 and run.stdout=='OK\n'*8 and run.stderr=='','native baseline integer/source/slice mismatch')
      mutations=[('factor20-to21','20ULL*j','21ULL*j'),('negative-branch-zero','value=(10000000000000000ULL-e);','value=0ULL;'),('add-only-one-word','add_magnitude(quad,temp,6ULL)','add_magnitude(quad,temp,1ULL)'),('truncated-loop','j<'+str(count)+'ULL','j<2ULL')]
      if fap:mutations.append(('Fap-scale100-to99','multiply_small(quad,6ULL,100ULL)','multiply_small(quad,6ULL,99ULL)'))
      mutation_rows=[]
      for name,old,new in mutations:
        need(fragment.count(old)==1,'mutation target must occur once in actual segment: '+name);mutated=fragment.replace(old,new);ms=a.out/(concrete+'.'+name+'.c');ms.write_text(original[:start]+mutated+original[end:]);mh=a.out/(concrete+'.'+name+'.test.c');mh.write_text(harness_text(ms.name,mutated));me=a.out/(concrete+'.'+name+'.test');mc=[compiler,'-std=c11','-O2',str(mh),'-o',str(me)];b=subprocess.run(mc,capture_output=True,text=True);need(b.returncode==0,'mutant compile: '+name+': '+b.stderr);r=subprocess.run([str(me)],capture_output=True,text=True);need(r.returncode>0,'wrong source was not rejected by numerical/slice check: '+name);mutation_rows.append(dict(name=name,original_fragment=old,mutated_fragment=new,source_sha256=sha(ms),harness_sha256=sha(mh),command=mc,exitcode=r.returncode,stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),stderr_sha256=hashlib.sha256(r.stderr.encode()).hexdigest()))
      rows.append(dict(formal_source=str(lean),formal_sha256=sha(lean),concrete_source=str(source),source_sha256=sha(source),input=str(data),input_sha256=sha(data),count=count,grid=131072 if fap else 16777216,Fap_extra100=fap,raw_quad=str(raw),scaled_quad=str(expected),extracted_segment_sha256=hashlib.sha256(fragment.encode()).hexdigest(),segment_byte_start=start,segment_byte_end=end,command=cmd,harness_sha256=sha(harness),executable_sha256=sha(exe),cases=8,mutations=mutation_rows))
    atomic(a.out/'RESULT.json',dict(status='PASS_NATIVE_QUAD_CORROBORATION_AND_WRONG_SOURCE_CONTROLS_ONLY',source_first_PV_complete=False,proof=False,seed=seed,rows=rows,script_sha256=sha(Path(__file__)),python=sys.version,python_optimization=sys.flags.optimize,compiler=str(compiler),compiler_sha256=sha(Path(compiler)),compiler_version=subprocess.run([compiler,'--version'],check=True,capture_output=True,text=True).stdout,seconds=time.monotonic()-began))
    print('PASS native quad corroboration: eight cases per source, four common wrong-source controls plus Fap ×100; tests only')
if __name__=='__main__':main()
