"""Exercise the actual saved-index validator CLI in all Python optimization modes."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys
B=Path(__file__).resolve().parent;R=B.parents[1]
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    out=a.out.resolve();need(out.is_relative_to(R) and not out.exists(),'fresh owned output');out.mkdir(parents=True)
    original=B/'RESUME_ACTUAL_SOURCE_PROGRESS_V14.json';expected=original.read_bytes();records=[]
    for label,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
        target=out/(label+'.json');command=[sys.executable,*flags,str(B/'build_progress_v14.py'),'--out',str(target)]
        for suffix,success in [('positive',True),('existing',False)]:
            q=subprocess.run(command,capture_output=True,text=True)
            need((q.returncode==0)==success,'unexpected real CLI '+label+suffix)
            need(target.read_bytes()==expected,'index differs or existing target changed')
            name=label+'-'+suffix
            (out/(name+'.stdout')).write_text(q.stdout);(out/(name+'.stderr')).write_text(q.stderr)
            records.append(dict(name=name,command=command,exit_code=q.returncode,expected_success=success,
                stdout_sha256=sha(out/(name+'.stdout')),stderr_sha256=sha(out/(name+'.stderr'))))
    need(len(records)==6 and original.read_bytes()==expected,'six actual routes and original unchanged')
    d=dict(status='PASS_SAVED_INDEX_SIX_ACTUAL_CLI_ROUTES_NORMAL_O_OO',proof_replay=False,
        script_sha256=sha(B/'build_progress_v14.py'),index_sha256=sha(original),records=records)
    t=out/'RECEIPT.pending';t.write_text(json.dumps(d,indent=2)+'\n');os.replace(t,out/'RECEIPT.json');print(d['status'])
if __name__=='__main__':main()
