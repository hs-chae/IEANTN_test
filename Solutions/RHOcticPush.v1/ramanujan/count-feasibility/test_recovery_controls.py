#!/usr/bin/env python3
"""Bounded rejection controls, including actual CLIs in normal/-O/-OO.
These test acceptance guards; they are not mathematical verification receipts.
"""
from pathlib import Path
import argparse, importlib.util, json, os, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent

def worker():
    p=HERE/'recover_count.py';s=importlib.util.spec_from_file_location('recovery',p)
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
    rows=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,FileNotFoundError,KeyError,TypeError):rows.append(dict(name=name,status='REJECT'))
        else:raise RuntimeError('mutation accepted:'+name)
    target='Exact.part'
    if m.reports("'Exact.part' does not depend on any axioms",[target],True)!={target:[]}:
        raise RuntimeError('positive empty-axiom reflection failed')
    rows.append(dict(name='positive_empty_axiom_report',status='PASS'))
    for name,text in [
        ('native_execution',"'Exact.part' depends on axioms: [Lean.ofReduceBool]"),
        ('admit',"'Exact.part' depends on axioms: [sorryAx]"),
        ('nonempty_numeric_leaf',"'Exact.part' depends on axioms: [propext]"),
        ('wrong_symbol',"'Other.part' does not depend on any axioms"),
        ('missing_report',''),
        ('duplicate_report',"'Exact.part' does not depend on any axioms\n'Exact.part' does not depend on any axioms")]:
        reject(name,lambda text=text:m.reports(text,[target],True))
    with tempfile.TemporaryDirectory(prefix='rh-count-control-')as d:
        root=Path(d);r=root/'bad.json'
        r.write_text('{"a":1,"a":2}');reject('duplicate_JSON_key',lambda:m.read(r))
        r.write_text('{"a":NaN}');reject('nonfinite_JSON',lambda:m.read(r))
        for value in [False,True,1,-9]:
            r.write_text(json.dumps(dict(status='PASS',returncode=value)))
            reject('compiler_returncode_'+str(value),lambda:m.audit_receipt(root,{},dict(module='Bad'),r))
        r.write_text(json.dumps(dict(status='FAILED_ATTEMPT_PRESERVED',returncode=0)))
        reject('failed_attempt_not_acceptance',lambda:m.audit_receipt(root,{},dict(module='Bad'),r))
    print(json.dumps(dict(status='PASS_GUARD_CONTROLS',optimization=sys.flags.optimize,rows=rows)))

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--worker',action='store_true');p.add_argument('--out',type=Path)
    a=p.parse_args()
    if a.worker:worker();return
    if a.out is None:raise ValueError('--out required')
    if a.out.exists():raise ValueError('fresh control receipt required')
    results=[];env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    for flags in [[],['-O'],['-OO']]:
        cp=subprocess.run([sys.executable,*flags,str(Path(__file__).resolve()),'--worker'],env=env,capture_output=True,text=True)
        if cp.returncode!=0:raise RuntimeError('guard control subprocess failed:'+cp.stderr)
        row=json.loads(cp.stdout);results.append(row)
        # Actual acceptance CLI routes must reject missing/incomplete studies.
        with tempfile.TemporaryDirectory(prefix='rh-count-cli-')as d:
            for route in ['--verify','--check']:
                cmd=[sys.executable,*flags,str(HERE/'recover_count.py'),route,d]
                bad=subprocess.run(cmd,env=env,capture_output=True,text=True)
                if bad.returncode==0:raise RuntimeError('incomplete actual CLI accepted')
                row['rows'].append(dict(name='actual_CLI_'+route,status='REJECT',command=cmd))
    data=dict(status='PASS_ALL_OPTIMIZATION_MODES',results=results,
        scope='Guard unit tests plus actual incomplete-study CLI rejection; not an accepted mathematical count.')
    a.out.write_text(json.dumps(data,indent=2)+'\n');print(data['status'])
if __name__=='__main__':main()
