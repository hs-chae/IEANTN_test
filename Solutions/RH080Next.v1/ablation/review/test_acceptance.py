#!/usr/bin/env python3
"""Negative CLI controls against copied review receipts; originals immutable."""
import argparse,hashlib,json,shutil,subprocess,sys
from pathlib import Path
TRIALS=['fixed_width-B_named-r1','fixed_width-C_network-r0','prime_index-B_named-r1']
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();need(not a.output.exists(),'Fresh control directory required');a.output.mkdir()
    checker=Path(__file__).with_name('check_reviews.py');records=[]
    for mutation in ['nonstandard-axiom','missing-real-dependency','missing-child-route']:
        fixture=a.output/mutation;fixture.mkdir()
        for trial in TRIALS:
            name=trial+'-replay-v4';target=fixture/name;target.mkdir();shutil.copy2(a.root/(name+'.INPUTS.json'),fixture/(name+'.INPUTS.json'));shutil.copy2(a.root/name/'result.json',target/'result.json');shutil.copytree(a.root/name/'submission',target/'submission')
        run=fixture/(TRIALS[0]+'-replay-v4');export=run/'submission'
        if mutation=='missing-child-route':(export/'Transfer.stdout').unlink()
        else:
            theorem=export/'THEOREMS.json';rows=json.loads(theorem.read_text());root=next(x for x in rows if x['declaration']=='PopulationTransfer.good_three')
            if mutation=='nonstandard-axiom':root['axioms'].append('Forbidden.applicationOutput')
            else:root['application_closure'].remove('RH080Exposure.Estimates.sparse')
            theorem.write_text(json.dumps(rows));lockpath=export/'LOCK.json';lock=json.loads(lockpath.read_text())
            for item in lock['files']:
                if item['path']=='THEOREMS.json':item['sha256']=sha(theorem)
            lockpath.write_text(json.dumps(lock));backendpath=run/'result.json';backend=json.loads(backendpath.read_text());backend['artifact_export']['lock_sha256']=sha(lockpath);backendpath.write_text(json.dumps(backend))
        for mode in ['', '-O','-OO']:
            name=mode or 'normal';receipt=a.output/(mutation+'.'+name+'.json');log=a.output/(mutation+'.'+name+'.log');command=[sys.executable]+([mode] if mode else [])+[str(checker),'--root',str(fixture),'--attempt','4','--output',str(receipt)];child=subprocess.run(command,capture_output=True,text=True);log.write_text(child.stdout+child.stderr)
            need(child.returncode!=0 and not receipt.exists(),'Negative control accepted: '+mutation+'/'+name)
            records.append(dict(mutation=mutation,mode=name,command=command,exitcode=child.returncode,rejected=True,log_sha256=sha(log)))
    result=dict(status='PASS_ALL9_NEGATIVE_CONTROLS',cases=records,checker_sha256=sha(checker),original_receipts_unchanged=True)
    (a.output/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS_ALL9_NEGATIVE_CONTROLS',a.output/'RESULT.json')
if __name__=='__main__':main()
