#!/usr/bin/env python3
"""Exercise actual cold-validator CLIs on the completed real run and isolated mutations."""
import argparse, hashlib, json, os, shutil, subprocess, sys
from pathlib import Path
from compile_verified_batch import atomic, need, sha
HERE=Path(__file__).resolve().parent


def replace_local(path,data):
    need(path.is_symlink(),'Mutation must replace a fixture symlink, never original proof bytes')
    path.unlink();path.write_bytes(data)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run',required=True,type=Path);ap.add_argument('--out',required=True,type=Path)
    a=ap.parse_args();base=a.run.resolve();out=a.out.resolve()
    need((base/'RESULT.json').is_file(),'Complete actual source-cold run required')
    need(not out.exists(),'Fresh experiment-owned controls directory required');out.mkdir(parents=True)
    plan=json.loads((base/'PLAN.json').read_text());need(plan['source_cold'] and not plan['application_object_fallback'],'Wrong actual experiment')
    name='FFTMainSourceNormAudit';need(any(r['module']==name for r in plan['source_rows']),'Actual full program audit missing')
    cases=[];cleanup=[]
    for optimize in [0,1,2]:
        flags=[] if optimize==0 else ['-O'] if optimize==1 else ['-OO']
        positive=[sys.executable,*flags,str(HERE/'reproduce_main_source_cold.py'),'--verify-only',str(base)]
        label='real-positive-'+str(optimize);o=out/(label+'.stdout');e=out/(label+'.stderr')
        with o.open('xb') as stdout,e.open('xb') as stderr:r=subprocess.run(positive,stdout=stdout,stderr=stderr)
        need(r.returncode==0 and 'PASS_STRICT_SOURCE_COLD_REVALIDATION' in o.read_text(),'Actual positive validator failed '+label)
        cases.append(dict(label=label,optimization=optimize,command=positive,exitcode=r.returncode,stdout_sha256=sha(o),stderr_sha256=sha(e)))
        for kind in ['panic-exit0','changed-proof-object','missing-compiler-receipt','omitted-source-row']:
            fixture=out/('fixture-'+kind+'-'+str(optimize));fixture.mkdir()
            for item in base.iterdir():
                if item.name in ['PLAN.json','RESULT.json']:shutil.copy2(item,fixture/item.name)
                elif item.name in ['source','objects','logs']:
                    dest=fixture/item.name;dest.mkdir()
                    for child in item.iterdir():(dest/child.name).symlink_to(child.resolve(),target_is_directory=child.is_dir())
                else:(fixture/item.name).symlink_to(item.resolve(),target_is_directory=item.is_dir())
            mutated={}
            if kind=='panic-exit0':
                target=fixture/'logs'/(name+'.stdout');data=(base/'logs'/(name+'.stdout')).read_bytes()+b'\nPANIC: controlled exit-zero diagnostic mutation\n'
                replace_local(target,data)
                receipt=fixture/(name+'.COMPILED.json');record=json.loads(receipt.read_text());record['stdout_sha256']=sha(target)
                replace_local(receipt,(json.dumps(record,indent=2)+'\n').encode());mutated={'log_sha256':sha(target),'receipt_sha256':sha(receipt),'compiler_exitcode':record['exitcode']}
            elif kind=='changed-proof-object':
                target=fixture/'objects'/(name+'.olean');replace_local(target,(base/'objects'/(name+'.olean')).read_bytes()+b'controlled-mutation');mutated={'object_sha256':sha(target)}
            elif kind=='missing-compiler-receipt':
                target=fixture/(name+'.COMPILED.json');need(target.is_symlink(),'Expected owned fixture receipt link');target.unlink();mutated={'missing_receipt':target.name}
            else:
                target=fixture/'PLAN.json';record=json.loads(target.read_text());record['source_rows']=[r for r in record['source_rows'] if r['module']!=name];target.write_text(json.dumps(record,indent=2)+'\n')
                result=fixture/'RESULT.json';record=json.loads(result.read_text());record['plan_sha256']=sha(target);record['modules']-=1;result.write_text(json.dumps(record,indent=2)+'\n');mutated={'plan_sha256':sha(target),'result_sha256':sha(result)}
            label=kind+'-'+str(optimize);o=out/(label+'.stdout');e=out/(label+'.stderr')
            command=[sys.executable,*flags,str(HERE/'reproduce_main_source_cold.py'),'--verify-only',str(fixture)]
            with o.open('xb') as stdout,e.open('xb') as stderr:r=subprocess.run(command,stdout=stdout,stderr=stderr)
            need(r.returncode!=0 and 'Traceback' in e.read_text(),'Actual negative CLI unexpectedly accepted '+label)
            cases.append(dict(label=label,optimization=optimize,command=command,exitcode=r.returncode,stdout_sha256=sha(o),stderr_sha256=sha(e),mutation=mutated))
            need(fixture.parent==out and not fixture.is_symlink(),'Cleanup target escaped experiment-owned fixture root')
            cleanup.append(str(fixture));shutil.rmtree(fixture)
    atomic(out/'RESULT.json',dict(status='PASS_ACTUAL_MAIN_SOURCE_COLD_VALIDATOR_ALL_OPTIMIZATIONS_AND_MUTATIONS',
      real_run=str(base),real_result_sha256=sha(base/'RESULT.json'),controller_sha256=sha(HERE/'reproduce_main_source_cold.py'),validator_sha256=sha(Path(__file__)),
      positives=3,negative_rejections=12,cases=cases,cleaned_regenerable_fixture_directories=cleanup,
      original_proof_artifacts_modified=False,new_proofs_claimed=False))
    print('PASS actual source-cold validator3positive/12negative CLI routes; originals untouched')


if __name__=='__main__':main()
