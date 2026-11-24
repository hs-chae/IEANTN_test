#!/usr/bin/env python3
"""Exercise the actual acceptance CLI in normal/-O/-OO, preserving receipts.

Mutant copies are reproducible experiment-owned scratch. Only those verified
copies are removed after the subprocess outcome and hashes have been recorded.
The accepted foundation and source/proof artifacts are never modified.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, shutil, subprocess, sys, time
H = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('grammar_acceptance',H/'reproduce.py')
V = importlib.util.module_from_spec(spec)
spec.loader.exec_module(V)
need,sha,read,save = V.need,V.sha,V.read,V.save

def copy_run(original,target):
    shutil.copytree(original,target,symlinks=True)
    for link in (target/'union').rglob('*.olean'):
        old = link.resolve()
        if old.is_relative_to(original):
            link.unlink()
            link.symlink_to(target/old.relative_to(original))

def mutate(kind,target):
    rr = read(target/'RESULT.json')
    if kind == 'source':
        p=target/'source/CounterGrammar.lean';p.write_bytes(p.read_bytes()+b'\n-- mutation\n')
    elif kind == 'object':
        p=target/'objects/CounterGrammar.olean';p.write_bytes(p.read_bytes()+b'mutation')
    elif kind in {'foreign_dependency','omitted_dependency'}:
        row = rr['dependency_probes'][1]
        p=target/'dependencies'/(row['module']+'.stdout')
        lines=p.read_text().splitlines()
        if kind == 'foreign_dependency':
            p.write_text('\n'.join(lines+['/tmp/not-an-accepted-application-object.olean'])+'\n')
        else:
            generic=[x for x in lines if '/lib/lean/Init.olean' in x]
            need(generic,'actual valid generic dependency for omission control')
            p.write_text(generic[0]+'\n')
        row['stdout_sha256']=sha(p)
    elif kind in {'native_axiom','missing_value_path'}:
        p=target/'logs/CounterSyntaxAudit.stdout'
        lines=p.read_text().splitlines();changed=False
        marker='COUNTER_GRAMMAR_THEOREM ' if kind=='native_axiom' else 'COUNTER_GRAMMAR_VALUE_PATH '
        for i,line in enumerate(lines):
            if marker+'{' not in line:
                continue
            prefix,data=line.split(marker,1);value=json.loads(data)
            if kind=='native_axiom':
                value['axioms']=['Lean.ofReduceBool']
            else:
                value['required']=value['required'][:-1]
                value['required_count']=len(value['required'])
            lines[i]=prefix+marker+json.dumps(value,separators=(',',':'))
            changed=True;break
        need(changed,'actual logged theorem/path to mutate')
        p.write_text('\n'.join(lines)+'\n')
        rr['build'][-1]['stdout_sha256']=sha(p)
    elif kind == 'float_counter':
        rr['fresh_scientific_sources']=4.0
    elif kind == 'bool_counter':
        rr['fresh_audit_sources']=True
    elif kind == 'bool_resource':
        rr['resource_admission']['max_parallel_jobs']=True
    elif kind == 'duplicate_JSON':
        p=target/'RESULT.json';text=p.read_text();p.write_text(text.replace('{','{"status":"duplicate",',1));return
    else:
        raise ValueError('unknown mutation')
    save(target/'RESULT.json',rr)

def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--run',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();original=a.run.resolve();out=a.out.resolve()
    V.validate(original)
    need(not out.exists() and out.parent.is_dir(),'fresh owned controls namespace')
    out.mkdir();scratch=out/'experiment-owned-regenerable-copies';scratch.mkdir()
    cases=[('valid',None),('source','source/object hash association'),
           ('object','source/object hash association'),
           ('foreign_dependency','foreign/drifted application object'),
           ('omitted_dependency','omitted declared application import'),
           ('native_axiom','nonstandard or native numerical proof axiom'),
           ('missing_value_path','final source-run consumes'),
           ('float_counter','strict integer result metadata'),
           ('bool_counter','strict integer result metadata'),
           ('bool_resource','strict integer resource admission'),
           ('duplicate_JSON','duplicate JSON key'),('relocated',None)]
    rows=[];start=time.monotonic()
    for opt in ['', '-O','-OO']:
        for kind,expected in cases:
            label=(opt or 'normal').replace('-','')+'-'+kind
            target=original if kind=='valid' else scratch/label
            if kind!='valid':
                copy_run(original,target)
                if kind!='relocated':mutate(kind,target)
            cmd=[sys.executable]+([opt]if opt else[])+[str(H/'reproduce.py'),'--verify',str(target)]
            t=time.monotonic();cp=subprocess.run(cmd,capture_output=True,text=True)
            stem=out/label;so=stem.with_suffix('.stdout');se=stem.with_suffix('.stderr')
            so.write_text(cp.stdout);se.write_text(cp.stderr)
            need((cp.returncode==0) if expected is None else
                 (cp.returncode!=0 and expected in cp.stderr),'actual CLI gate:'+label)
            if expected is None:
                parsed=json.loads(cp.stdout)
                need(parsed['status']=='PASS_COUNTER_GRAMMAR_READBACK','valid actual readback')
            rows.append({'case':label,'command':cmd,'returncode':cp.returncode,
                         'seconds':time.monotonic()-t,'expected_rejection':expected,
                         'stdout':so.name,'stdout_sha256':sha(so),
                         'stderr':se.name,'stderr_sha256':sha(se),
                         'mutated_result_sha256':sha(target/'RESULT.json'),
                         'cleanup':'original preserved' if kind=='valid' else 'verified regenerable mutant copy removed'})
            if kind!='valid':
                need(target.parent==scratch and target.name==label and
                     scratch.parent==out and target.resolve().is_relative_to(out),
                     'verified owned cleanup target')
                shutil.rmtree(target)
            print(label,cp.returncode,flush=True)
    need(len(rows)==36 and not list(scratch.iterdir()),'all normal/O/OO controls and owned cleanup')
    result={'status':'PASS_ALL36_COUNTER_GRAMMAR_CLI_CONTROLS',
            'controller_sha256':sha(H/'reproduce.py'),'controls_sha256':sha(__file__),
            'accepted_result_sha256':sha(original/'RESULT.json'),'seconds':time.monotonic()-start,
            'cases':rows,'cleanup':'Only copied experiment-owned regenerable mutant trees removed; accepted originals/evidence preserved.'}
    save(out/'RESULT.json',result)
    print(result['status'])
if __name__=='__main__':main()
