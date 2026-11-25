#!/usr/bin/env python3
"""Actual all-mode source/validator controls and theorem-assumption/range failures."""
import argparse,concurrent.futures,hashlib,json,os,subprocess,sys
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',type=Path,required=True);ap.add_argument('--accepted',type=Path,required=True);ap.add_argument('--run',type=Path,required=True)
    a=ap.parse_args();need(not os.path.lexists(a.run),'Fresh controls required');a.run.mkdir(parents=True);here=Path(__file__).resolve().parent
    accepted=json.loads((a.accepted/'RESULT.json').read_text());plan=json.loads((a.accepted/'PLAN.json').read_text())
    need(accepted['status']=='PASS_COMPLETE_FRESH_SOURCE_ONLY_FINITE_FRONTIER_KERNEL_CLOSURE'and accepted['module_count']==12,'Actual12-source positive required')
    need(plan['controller_sha256']==sha(here/'reproduce.py')and plan['manifest_sha256']==sha(here/'SOURCE_MANIFEST.json'),'Accepted/controller/source association')
    need(accepted['plan_sha256']==sha(a.accepted/'PLAN.json')and accepted['audit_stdout_sha256']==sha(a.accepted/'Audit.stdout'),'Accepted receipt association')
    for row in accepted['steps']:
        rel=row['module'].replace('.','/')
        need(sha(a.accepted/'source'/(rel+'.lean'))==row['source_sha256']and sha(a.accepted/'objects'/(rel+'.olean'))==row['object_sha256'],'Accepted source/object changed')
    rows=[]
    def child(name,mode,flags,success):
        command=[sys.executable,*mode,str(here/'reproduce.py'),*map(str,flags)];p=subprocess.run(command,capture_output=True)
        (a.run/(name+'.stdout')).write_bytes(p.stdout);(a.run/(name+'.stderr')).write_bytes(p.stderr)
        need((p.returncode==0)==success,'Unexpected child status '+name)
        return dict(name=name,command=command,exit_code=p.returncode,expected_success=success,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
    # Two independent cold positive runs, alongside the previously accepted normal run.
    with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
        futures=[pool.submit(child,label+'-positive',[mode],['--context',a.context,'--run',a.run/(label+'-positive')],True)for mode,label in [('-O','O'),('-OO','OO')]]
        for future in futures:rows.append(future.result())
    context=json.loads(a.context.read_text())
    for mode,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
        for kind in ['compiler','generic','revision','duplicate','source']:
            changed=dict(context);manifest=None
            if kind=='compiler':changed['compiler_sha256']='0'*64
            if kind=='generic':changed['generic_lean_path']=[]
            if kind=='revision':changed['generic_dependencies']=[dict(x)for x in context['generic_dependencies']];changed['generic_dependencies'][0]['revision']='0'*40
            if kind=='source':
                m=json.loads((here/'SOURCE_MANIFEST.json').read_text());m['modules'][0]['sha256']='0'*64;manifest=a.run/(label+'-bad-source.json');manifest.write_text(json.dumps(m))
            bad=a.run/(label+'-'+kind+'.json');bad.write_text(json.dumps(changed)if kind!='duplicate'else'{"compiler":1,"compiler":2}')
            dest=a.run/(label+'-'+kind)
            flags=['--context',bad,'--run',dest]
            if manifest:flags+=['--source-manifest',manifest]
            rows.append(child(label+'-'+kind,mode,flags,False));need(not(dest/'RESULT.json').exists(),'Rejected child emitted acceptance')
        old=sha(a.accepted/'RESULT.json');rows.append(child(label+'-reuse',mode,['--context',a.context,'--run',a.accepted],False));need(sha(a.accepted/'RESULT.json')==old,'Reuse control modified accepted receipt')
    compiler=context['compiler'];generic=context['generic_lean_path'];generic=generic.split(':')if isinstance(generic,str)else generic
    env=dict(os.environ,LEAN_PATH=':'.join([str(a.accepted/'objects'),*generic]))
    fixtures={
      'missing-table-input':'example : PrimeInterval.v5.closed_width1550 := PrimeInterval.v5.challenge_closed_width1550\n',
      'missing-log-gap-input':'example : PrimeInterval.v5.strict_log_squared := PrimeInterval.v5.challenge_strict_log_squared\n',
      'invalid-terminal-endpoint':'example (h : PrimeGapTable.v1.gaps) : ∃ q : ℕ, q.Prime ∧ (18446744073709551557 : ℝ) < q ∧ (q : ℝ) < 18446744073709551557 + (1550+1) := by\n  exact RH080.FiniteFrontier.strict_width1550_add (x := 18446744073709551557) (ε := 1) h (by norm_num) (by norm_num [RH080.FiniteFrontier.terminal]) (by norm_num)\n',
      'invalid-small-domain':'example (h : FiniteLogSquaredPrimeGaps.v1.gaps) (h42 : (7 : ℝ) ≤ Real.exp 42) : ∃ q : ℕ, q.Prime ∧ (7 : ℝ) < q ∧ (q : ℝ) < 7 + (Real.log 7)^2 := by\n  exact RH080.FiniteFrontier.strict_log_squared (x := 7) h (by norm_num) h42\n'}
    lean=[]
    for name,body in fixtures.items():
        source=a.run/(name+'.lean');source.write_text('import FiniteNetworkIntegration\n'+body)
        command=[compiler,'-j2','-R',str(a.run),str(source)];p=subprocess.run(command,env=env,capture_output=True)
        output=p.stdout.decode()+p.stderr.decode();need(p.returncode!=0 and 'error:'in output and 'unknown module'not in output,'Expected semantic Lean failure absent: '+name)
        (a.run/(name+'.Lean.stdout')).write_bytes(p.stdout);(a.run/(name+'.Lean.stderr')).write_bytes(p.stderr)
        lean.append(dict(name=name,command=command,exit_code=p.returncode,source_sha256=sha(source),output_sha256=hashlib.sha256(p.stdout+p.stderr).hexdigest()))
    result=dict(status='PASS_FINITE_FRONTIER_NORMAL_O_OO_AND_PROOF_SOURCE_RANGE_CONTROLS',
        accepted_normal_receipt_sha256=sha(a.accepted/'RESULT.json'),actual_additional_cold_kernel_runs=2,actual_cli_negative_controls=18,actual_lean_negative_controls=4,
        controller_sha256=sha(Path(__file__)),rows=rows,lean_failures=lean,source_first_PV=False)
    temp=a.run/'RESULT.json.tmp';temp.write_text(json.dumps(result,indent=2)+'\n');os.link(temp,a.run/'RESULT.json');temp.unlink()
    print(json.dumps({k:result[k]for k in ['status','actual_additional_cold_kernel_runs','actual_cli_negative_controls','actual_lean_negative_controls']}))

if __name__=='__main__':main()
