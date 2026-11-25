#!/usr/bin/env python3
"""Rebuild the scalar Lean theorem and execute the bounded external ANT probes."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,sys,re,shutil

def need(c,msg):
 if not c:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--flint-python',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'Fresh output required');a.out.mkdir(parents=True);here=Path(__file__).resolve().parent;start=time.monotonic();ctx=json.loads(a.context.read_text());compiler=Path(ctx['compiler']);need(sha(compiler)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Wrong Lean compiler hash');generic=ctx['generic_lean_path'];env=dict(os.environ,LEAN_PATH=generic)
 available=next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:'));need(available>=(256+32)*2**30,'Host reserve plus worker allowance unavailable');disk=shutil.disk_usage(a.out).free;need(disk>=2**30,'Separate free disk insufficient')
 versions=json.loads(subprocess.check_output([str(a.flint_python),'-c','import sys,json,flint;print(json.dumps({"Python":sys.version,"python_flint":flint.__version__}))'],text=True));need(versions['python_flint']=='0.9.0','Pinned python-flint0.9.0 required')
 frozen=a.out/'source';frozen.mkdir();(frozen/'RetunedBudgetBarrier.lean').write_bytes((here/'RetunedBudgetBarrier.lean').read_bytes());(frozen/'probe.py').write_bytes((here/'probe.py').read_bytes());commands=[]
 jobs=[('Lean',[str(compiler),'-o',str(a.out/'RetunedBudgetBarrier.olean'),'RetunedBudgetBarrier.lean'],frozen,env),('Arb',[str(a.flint_python),str(frozen/'probe.py'),'--out',str(a.out/'probe')],here,None)]
 for label,cmd,cwd,environ in jobs:
  command=['prlimit','--as=34359738368','--','/usr/bin/time','-v','-o',str(a.out/(label+'.time'))]+cmd;t=time.monotonic()
  with(a.out/(label+'.stdout')).open('w')as out,(a.out/(label+'.stderr')).open('w')as err:r=subprocess.run(command,cwd=cwd,env=environ,stdout=out,stderr=err)
  commands.append({'label':label,'command':command,'seconds':time.monotonic()-t,'returncode':r.returncode,'stdout_sha256':sha(a.out/(label+'.stdout')),'stderr_sha256':sha(a.out/(label+'.stderr')),'time_sha256':sha(a.out/(label+'.time'))});need(r.returncode==0,label+'failed')
 log=(a.out/'Lean.stdout').read_text();audits=re.findall(r'depends on axioms: \[([^]]*)\]',log);need(len(audits)==1 and set(x.strip()for x in audits[0].split(','))<={'propext','Classical.choice','Quot.sound'},'Unapproved axiom closure');need(sha(frozen/'RetunedBudgetBarrier.lean')==sha(here/'RetunedBudgetBarrier.lean'),'Lean source changed');need(sha(frozen/'probe.py')==sha(here/'probe.py'),'Probe source changed');record={'status':'PASS_KERNEL_SCALAR_THEOREM_AND_EXTERNAL_BOUNDED_PROBE','scope':'No full analytic source extension or new prime theorem is claimed','commands':commands,'seconds':time.monotonic()-start,'compiler_sha256':sha(compiler),'context_sha256':sha(a.context),'software':versions,'source_hashes':{'RetunedBudgetBarrier.lean':sha(frozen/'RetunedBudgetBarrier.lean'),'probe.py':sha(frozen/'probe.py')},'object_sha256':sha(a.out/'RetunedBudgetBarrier.olean'),'admission_available_RAM_bytes':available,'admission_free_disk_bytes':disk,'per_process_AS_bytes':32*2**30};temp=a.out/'RESULT.pending';temp.write_text(json.dumps(record,indent=2)+'\n');temp.rename(a.out/'RESULT.json');print(record['status'])
if __name__=='__main__':main()
