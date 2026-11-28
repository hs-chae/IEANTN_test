#!/usr/bin/env python3
"""Actual wrapper/exec inheritance and fail-closed CLI controls in all Python modes."""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise RuntimeError(message)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def publish(path,value):
    need(not path.exists(),'Fresh final control receipt required');temp=path.with_name('.'+path.name+'.tmp')
    with temp.open('x')as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(temp,path)
    finally:temp.unlink()

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'Fresh controls required');a.out.mkdir()
    before={name:Path('/sys/kernel/mm/transparent_hugepage/'+name).read_bytes()for name in['enabled','defrag']}
    child=a.out/'child_probe.py';child.write_text("import ctypes,json,os\nfrom pathlib import Path\np=ctypes.CDLL(None).prctl\np.restype=ctypes.c_int\ns=Path('/proc/self/status').read_text()\nx=next(l.split(':',1)[1].strip()for l in s.splitlines()if l.startswith('THP_enabled:'))\nv=p(42,0,0,0,0)\nif v!=1 or x!='0':raise RuntimeError('Exec did not inherit process-only page policy')\nprint(json.dumps(dict(PR_GET=v,THP_enabled=x,PID=os.getpid())))\n")
    records=[];wrapper=HERE/'generic_page_policy_exec.py'
    for mode in range(3):
        flags=['-'+'O'*mode]if mode else[];receipt=a.out/('policy-'+str(mode)+'.json')
        command=[sys.executable,*flags,str(wrapper),'--disable-thp','--receipt',str(receipt),'--',sys.executable,str(child)]
        r=subprocess.run(command,capture_output=True,text=True)
        need(r.returncode==0 and receipt.is_file(),'Actual page-policy exec failed');v=json.loads(receipt.read_text());observed=json.loads(r.stdout)
        need(v['PR_GET_after']==observed['PR_GET']==1 and v['proc_THP_enabled']==observed['THP_enabled']=='0','Actual exec policy mismatch')
        need(v['status']=='VERIFIED_PROCESS_PAGE_POLICY_BEFORE_EXEC_NOT_CHILD_OR_PROOF_ACCEPTANCE','Pre-exec receipt overclaims acceptance')
        records.append(dict(case='positive',mode=mode,command=command,returncode=r.returncode,receipt_sha256=sha(receipt),child_observation=observed))
        for case in ['missing-policy','missing-command','relative-executable','unknown-option','existing-receipt','missing-executable']:
            output=a.out/(case+'-'+str(mode)+'.json');cmd=list(command);cmd[cmd.index('--receipt')+1]=str(output)
            if case=='missing-policy':cmd.remove('--disable-thp')
            elif case=='missing-command':cmd=cmd[:cmd.index('--')+1]
            elif case=='relative-executable':cmd[cmd.index('--')+1]='python3'
            elif case=='unknown-option':cmd.insert(cmd.index('--'),'--unknown-policy')
            elif case=='existing-receipt':output.write_text('preserve-existing-bytes\n')
            else:cmd[cmd.index('--')+1]='/does/not/exist'
            q=subprocess.run(cmd,capture_output=True,text=True)
            need(q.returncode!=0 and not q.stdout,'Invalid CLI executed the child: '+case)
            need(output.read_text()=='preserve-existing-bytes\n'if case=='existing-receipt'else not output.exists(),'Invalid CLI altered/emitted resource receipt')
            records.append(dict(case=case,mode=mode,command=cmd,returncode=q.returncode))
    for name,raw in before.items():need(Path('/sys/kernel/mm/transparent_hugepage/'+name).read_bytes()==raw,'Global THP setting changed')
    publish(a.out/'RESULT.json',dict(status='PASS_3_ACTUAL_PROCESS_POLICY_EXEC_INHERITANCE_18_CLI_REJECTIONS',records=records,wrapper_sha256=sha(wrapper),harness_sha256=sha(Path(__file__)),host_global_THP_settings_unchanged=True,ordinary_numerical_certificate_or_PV_claimed=False))
    print('PASS page-policy exec:3 actual inherited-policy positives,18 CLI rejections')
if __name__=='__main__':main()
