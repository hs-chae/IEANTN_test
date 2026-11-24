#!/usr/bin/env python3
"""Actual portable-readback CLI mutations; preserves the completed control.
Temporary copies are deterministic, experiment-owned and removed only after
each rejection is recorded. No original proof, source or result is edited.
"""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile, time

HERE=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def save(p,d):Path(p).write_text(json.dumps(d,indent=2)+'\n')

def main():
    a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--run',type=Path,required=True)
    a.add_argument('--out',type=Path,required=True);x=a.parse_args();run=x.run.resolve()
    if x.out.exists():raise ValueError('Fresh control receipt required')
    r=read(run/'RESULT.json')
    if r['smoke']is not True or r['exact_count']!=[1000,168]:raise ValueError('Small exact fixture only')
    if sum(p.stat().st_size for p in run.rglob('*')if p.is_file())>1<<30:
        raise ValueError('Bounded fixture copy required')
    original=sha(run/'RESULT.json');script=HERE/'portable/reproduce.py';rows=[]
    for flags in [[],['-O'],['-OO']]:
        cmd=[sys.executable,*flags,str(script),'--check',str(run)]
        cp=subprocess.run(cmd,capture_output=True,text=True)
        if cp.returncode!=0:raise RuntimeError('Positive readback failed:'+cp.stderr[-1000:])
        rows.append(dict(mode=flags,case='positive',returncode=cp.returncode,stdout=cp.stdout.strip()))
        for case in ['dropped_source','changed_typed_consumer','promote_smoke_to_full','boolean_chunk_count','boolean_compiler_status']:
            with tempfile.TemporaryDirectory(prefix='portable-control-',dir=x.out.parent)as d:
                fixture=Path(d)/'copy';shutil.copytree(run,fixture,symlinks=True)
                (Path(d)/'CONTROL_ONLY').write_text('Regenerable fixture; original retained.\n')
                rr=read(fixture/'RESULT.json')
                if case in ['dropped_source','changed_typed_consumer']:
                    ss=read(fixture/'SOURCES.json')
                    if case=='dropped_source':ss['modules'].pop(0)
                    else:
                        p=fixture/'source/RecoveredCountConsumer.lean';p.write_text('theorem wrong : True := True.intro\n')
                        next(q for q in ss['modules']if q['module']=='RecoveredCountConsumer')['source_sha256']=sha(p)
                    save(fixture/'SOURCES.json',ss);rr['source_manifest_sha256']=sha(fixture/'SOURCES.json')
                elif case=='promote_smoke_to_full':
                    rr.update(smoke=False,status='PASS_FULL_CLEAN_COUNT_AND_SOURCE_MODEL',
                        namespace='RamanujanPV.HighTransitionCount',exact_count=[1490000000000,55206486339])
                elif case=='boolean_chunk_count':rr['arithmetic_chunks']=True
                elif case=='boolean_compiler_status':
                    p=fixture/'replay/RESULT.json';v=read(p);v['records'][0]['exit_code']=False;save(p,v)
                save(fixture/'RESULT.json',rr)
                cmd=[sys.executable,*flags,str(script),'--check',str(fixture)]
                cp=subprocess.run(cmd,capture_output=True,text=True)
                if cp.returncode==0:raise RuntimeError('Mutation accepted:'+case+str(flags))
                rows.append(dict(mode=flags,case=case,returncode=cp.returncode,
                    stderr_sha256=hashlib.sha256(cp.stderr.encode()).hexdigest(),
                    fixture_removed_after_rejection=True))
    if sha(run/'RESULT.json')!=original:raise RuntimeError('Original fixture modified')
    save(x.out,dict(status='PASS18_ACTUAL_CLI_CONTROLS_NORMAL_O_OO',rows=rows,
        validator_sha256=sha(script),test_source_sha256=sha(__file__),
        original_RESULT_sha256=original,original_unchanged=True,created_unix=time.time(),
        cleanup='Only deterministic temporary copies created inside this control were removed; originals retained.'))
    print('PASS18_ACTUAL_CLI_CONTROLS_NORMAL_O_OO')
if __name__=='__main__':main()
