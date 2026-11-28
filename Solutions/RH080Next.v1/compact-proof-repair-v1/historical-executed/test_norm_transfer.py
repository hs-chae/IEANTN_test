#!/usr/bin/env python3
"""Bounded actual generic/S13 norm-transfer control; not an N24 output acceptance."""
import argparse,json,os,re,subprocess,sys,time
from pathlib import Path
D=Path('/data/ivy-rh080-next-20261125');Q=Path(__file__).resolve().parent
sys.path.insert(0,str(D/'network/Solutions/RH080Next.v1/dual'))
import resume_fft_dag_source_cold as old
from reproduce_dual import context,need,load,sha,publish

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run',type=Path,required=True)
    a=ap.parse_args();need(not os.path.lexists(a.run),'Fresh run required')
    membership=[line.split('::',1)[1]for line in Path('/proc/self/cgroup').read_text().splitlines()if line.startswith('0::')]
    need(len(membership)==1 and membership[0].endswith('.service'),'Owned actual unit required')
    cg=Path('/sys/fs/cgroup')/membership[0].lstrip('/')
    need((cg/'memory.max').read_text().strip()==str(64*2**30) and (cg/'memory.swap.max').read_text().strip()=='0','Actual64GiB/noSwap required')
    need(re.search(r'^THP_enabled:\s*0$',Path('/proc/self/status').read_text(),re.M),'THP0 required')
    need(set(os.sched_getaffinity(0))=={96,97,98,99},'Actual96-99 required')
    available=next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:'))
    need(available>=320*2**30,'Host reserve required')
    before=(cg/'memory.events').read_text();cp=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json');c=context(cp,old.R)
    bank=D/'w4-fresh-unlimited-actual-controls-v1/fresh-0';base=load(bank/'PLAN.json')
    accepted=[]
    for row in base['sources']:
        rec=old.receipt(bank,bank,row,c['compiler'],True)
        accepted.append(dict(module=row['module'],source_sha256=row['sha256'],object_sha256=rec['object_sha256'],receipt_sha256=sha(bank/(row['module']+'.COMPILED.json'))))
    need(len(accepted)==120,'Exact associated S13 accepted closure required')
    sources=[Q/'norm-transfer-controls-v1'/n for n in ['NormSymbolic.lean','NormTransferActual.lean']]
    need(all(not old.SOURCE_BAD.search(p.read_text())for p in sources),'Forbidden source construct')
    a.run.mkdir();objects=a.run/'objects';objects.mkdir()
    pins=[dict(path=str(p),sha256=sha(p))for p in[Path(__file__),*sources,cp,bank/'PLAN.json']]
    publish(a.run/'PLAN.json',dict(source_pins=pins,inherited_associated_S13_modules=accepted,physical_max_bytes=64*2**30,memory_events_before=before,actual_affinity=sorted(os.sched_getaffinity(0)),THP_enabled=0,virtual_AS='unlimited',compiler_sha256=c['compiler_sha256']))
    env=dict(os.environ,LEAN_PATH=str(objects)+':'+str(bank/'objects')+':'+c['generic_lean_path']);records=[]
    for p in sources:
        tm=a.run/(p.stem+'.time');obj=objects/(p.stem+'.olean');cmd=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as=unlimited','--stack='+str(256*2**20),'--',c['compiler'],'-j1','--root='+str(p.parent),'-o',str(obj),str(p)]
        tick=time.monotonic()
        with(a.run/(p.stem+'.stdout')).open('xb')as out,(a.run/(p.stem+'.stderr')).open('xb')as err:r=subprocess.run(cmd,env=env,stdout=out,stderr=err)
        stdout=(a.run/(p.stem+'.stdout')).read_text();stderr=(a.run/(p.stem+'.stderr')).read_text();timing=tm.read_text();peak=re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
        record=dict(module=p.stem,command=cmd,returncode=r.returncode,seconds=time.monotonic()-tick,peak_RSS_KiB=int(peak[0])if len(peak)==1 else None,source_sha256=sha(p),object_sha256=sha(obj)if obj.exists()else None,stdout_sha256=sha(a.run/(p.stem+'.stdout')),stderr_sha256=sha(a.run/(p.stem+'.stderr')),time_sha256=sha(tm))
        publish(a.run/(p.stem+'.COMPILED.json'),record)
        need(r.returncode==0 and not stderr and not old.BAD.search(stdout)and'warning:'not in stdout,'Actual helper proof compile failed')
        axes=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",stdout)
        expected=['RH080Next.PrivateNormProof.normFromOutput_of_totals']if p.stem=='NormSymbolic'else['RH080Next.PrivateNormTransferControl.actual13','RH080Next.PrivateNormTransferControl.symbolic24']
        need([root for root,names in axes]==expected,'Exact typed helper root audit missing')
        for root,names in axes:need(all(n.strip()in old.ALLOWED for n in names.split(',')if n.strip()),'Nonstandard execution axiom')
        need(len(peak)==1 and int(peak[0])>0 and re.search(r'Exit status:\s*0\s*$',timing)and'Command terminated by signal'not in timing,'Incomplete actual GNUtime')
        record['actual_axioms']=dict((root,[n.strip()for n in names.split(',')if n.strip()])for root,names in axes);records.append(record)
    for pin in pins:need(sha(Path(pin['path']))==pin['sha256'],'Executed source changed')
    after=(cg/'memory.events').read_text()
    def events(s):return dict((k,int(v))for k,v in(l.split()for l in s.splitlines()))
    need(events(after)['oom']==events(before)['oom']and events(after)['oom_kill']==events(before)['oom_kill'],'Actual OOM prevents acceptance')
    publish(a.run/'RESULT.json',dict(status='PASS_KERNEL_GENERIC_NORM_TRANSFER_AND_ACTUAL_ASSOCIATED_S13',records=records,original_S13_numeric_proofs_consumed=True,N24_concrete_output_proof=False,N24_arithmetic_target_proved_for_symbolic_output_with_original_explicit_totals=True,memory_events_before=before,memory_events_after=after,plan_sha256=sha(a.run/'PLAN.json'),new_axioms_sorry_native=False,source_first_PV_claimed=False))
    print('PASS ACTUAL S13 AND SYMBOLIC N24 TRANSFER',flush=True)
if __name__=='__main__':main()
