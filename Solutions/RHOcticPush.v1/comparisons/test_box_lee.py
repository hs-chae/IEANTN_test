#!/usr/bin/env python3
"""Actual strict readback CLI controls; mutate only an owned regenerable clone."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse, hashlib, json, os, shutil, subprocess, sys, time
H=Path(__file__).resolve().parent
CONTROLLER=H/'reproduce_box_lee.py'
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',required=True,type=Path);p.add_argument('--out',required=True,type=Path);a=p.parse_args()
    run=a.run.resolve();out=a.out.resolve();need((run/'RESULT.json').is_file(),'accepted original')
    need(not out.exists() and out.parent.is_dir() and not out.is_relative_to(run),'fresh separate owned output')
    original_result=(run/'RESULT.json').read_bytes();original_sha=sha(run/'RESULT.json')
    out.mkdir();clone=out/'mutant';shutil.copytree(run,clone,symlinks=True)
    rows=[];start=time.monotonic();modes=[[],['-O'],['-OO']]
    originals={p.relative_to(run):p.read_bytes() for p in run.rglob('*') if p.is_file() and not p.is_symlink()}
    def restore():
        for rel,data in originals.items():(clone/rel).write_bytes(data)
    def apply(name):
        restore();r=json.loads((clone/'RESULT.json').read_text())
        if name=='boolean-aggregate-RSS':r['sampled_peak_process_tree_RSS_bytes']=False
        elif name=='nonfinite-seconds':
            text=json.dumps(r);needle='"seconds": '+str(r['seconds']);need(needle in text,'time mutation target')
            (clone/'RESULT.json').write_text(text.replace(needle,'"seconds": 1e400',1));return
        elif name=='duplicate-axioms-payload':
            log=clone/'logs/BoxLeeAudit.stdout';text=log.read_text();needle='{"axioms":';need(needle in text,'payload target')
            log.write_text(text.replace(needle,'{"axioms":["native_decide"],"axioms":',1))
            r['compilations'][1]['stdout_sha256']=sha(log)
        elif name=='missing-direct-app-import':
            row=r['dependency_probes'][0];log=clone/'dependencies/BoxVsLee.stdout'
            lines=log.read_text().splitlines();selected=[x for x in lines if '/IEANTN/Vocabulary/RHOcticEvolution.olean' in x]
            need(len(selected)==1,'actual direct import line');log.write_text('\n'.join(x for x in lines if x not in selected)+'\n');row['stdout_sha256']=sha(log)
        elif name not in ['relocated-positive','restored-positive']:raise ValueError('unknown control')
        (clone/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n')
    def trial(name,mode,accept):
        label=name+'-O'+str(len(mode));cmd=[sys.executable,*mode,str(CONTROLLER),'--verify',str(clone)]
        cp=subprocess.run(cmd,capture_output=True,text=True)
        (out/(label+'.stdout')).write_text(cp.stdout);(out/(label+'.stderr')).write_text(cp.stderr)
        need((cp.returncode==0) is accept,'unexpected actual CLI decision:'+label)
        return {'case':name,'mode':mode,'command':cmd,'returncode':cp.returncode,'expected_accept':accept,'stdout_sha256':sha(out/(label+'.stdout')),'stderr_sha256':sha(out/(label+'.stderr'))}
    for name,accept in [('relocated-positive',True),('boolean-aggregate-RSS',False),('nonfinite-seconds',False),('duplicate-axioms-payload',False),('missing-direct-app-import',False),('restored-positive',True)]:
        apply(name)
        with ThreadPoolExecutor(max_workers=3) as pool:results=list(pool.map(lambda mode:trial(name,mode,accept),modes))
        rows.extend(results);(out/'PROGRESS.json').write_text(json.dumps({'completed':len(rows),'last':name})+'\n')
    restore();need(sha(run/'RESULT.json')==original_sha and (run/'RESULT.json').read_bytes()==original_result,'original preserved')
    need(len(rows)==18 and all(type(q['returncode']) is int and (q['returncode']==0) is q['expected_accept'] for q in rows),'all18 actual controls')
    r={'status':'PASS_ALL18_ACTUAL_BOX_LEE_CLI_CONTROLS','controller_sha256':sha(CONTROLLER),'test_source_sha256':sha(__file__),'accepted_run':str(run),'accepted_RESULT_sha256':original_sha,'rows':rows,'seconds':time.monotonic()-start,'original_accepted_run_unchanged':True,'scope':'Strict readback and relocation controls for one new mathematical comparison source; no new mathematical result or source-first PV claim.'}
    tmp=out/'.RESULT.pending';tmp.write_text(json.dumps(r,indent=2,allow_nan=False)+'\n');os.replace(tmp,out/'RESULT.json');print(r['status'])
if __name__=='__main__':main()
