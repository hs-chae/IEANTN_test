#!/usr/bin/env python3
"""Named-module counterpart of the existing flat development compiler.
Final source-fresh closure replay remains a distinct acceptance gate.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,resource,subprocess,time
R=Path(__file__).resolve().parents[5]
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--module',required=True)
    a.add_argument('--source-root',type=Path,required=True);a.add_argument('--out',type=Path,required=True)
    a.add_argument('--bank',type=Path,action='append',default=[]);x=a.parse_args()
    need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',x.module)is not None,'compiler module identity')
    need(not x.out.exists(),'fresh output');ctx=json.loads((R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text())
    need(sha(ctx['compiler'])==ctx['compiler_sha256'],'pinned compiler')
    source=x.source_root/Path(*x.module.split('.')).with_suffix('.lean');before=sha(source)
    x.out.mkdir(parents=True);objects=x.out/'objects';obj=objects/Path(*x.module.split('.')).with_suffix('.olean')
    obj.parent.mkdir(parents=True);union=x.out/'union';union.mkdir()
    for bank in x.bank:
        for old in bank.rglob('*.olean'):
            target=union/old.relative_to(bank);target.parent.mkdir(parents=True,exist_ok=True)
            if target.exists():need(sha(target)==sha(old),'consistent namespace overlay')
            else:target.symlink_to(old.resolve())
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    env['LEAN_PATH']=':'.join(map(str,[union,*ctx['generic_libraries']]))
    cmd=[ctx['compiler'],'--root='+str(x.source_root.resolve()),'-j1',str(source.resolve()),'-o',str(obj.resolve())]
    def limits():resource.setrlimit(resource.RLIMIT_AS,(64<<30,64<<30))
    start=time.monotonic()
    cp=subprocess.run(['/usr/bin/time','-v',*cmd],env=env,preexec_fn=limits,capture_output=True,text=True)
    (x.out/'stdout').write_text(cp.stdout);(x.out/'stderr').write_text(cp.stderr)
    need(before==sha(source),'source unchanged during compilation')
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",cp.stdout,re.S)
    if cp.returncode==0:
        need(not any(v in cp.stdout+cp.stderr for v in['sorryAx','Lean.ofReduceBool','declaration uses `sorry`']),'native/admit')
        for _,ax in rows:need({s.strip()for s in ax.split(',')}<={'propext','Classical.choice','Quot.sound'},'standard axioms')
    r=dict(status='PASS_DEV'if cp.returncode==0 else'FAIL_DEV',module=x.module,source=str(source),source_sha256=before,
        compiler_sha256=ctx['compiler_sha256'],command=cmd,LEAN_PATH=env['LEAN_PATH'],returncode=cp.returncode,
        seconds=time.monotonic()-start,development_only=True,axiom_reports=rows,
        stdout_sha256=sha(x.out/'stdout'),stderr_sha256=sha(x.out/'stderr'))
    if cp.returncode==0:
        r['object_sha256']=sha(obj);target=union/Path(*x.module.split('.')).with_suffix('.olean')
        need(not target.exists(),'new named module namespace');target.parent.mkdir(parents=True,exist_ok=True)
        target.symlink_to(obj.resolve())
    (x.out/'RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status']);raise SystemExit(cp.returncode)
if __name__=='__main__':main()
