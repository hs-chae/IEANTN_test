#!/usr/bin/env python3
"""Exercise actual validator and source-layout CLI in all optimization modes."""
from pathlib import Path
import argparse,copy,json,subprocess,hashlib,os
S=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
def need(c,m):
 if not c:raise ValueError(m)
O=a.out.resolve();need(not O.exists(),'fresh output required');O.mkdir(parents=True);j=json.loads((a.run_dir/'RESULT.json').read_text());rows=[]
for mode in ['', '-O','-OO']:
 prefix=['python3']+([mode]if mode else[]);label=mode[1:]if mode else'normal';accept=O/(label+'-accepted.json');cmd=prefix+[str(S/'verify_strong.py'),'--run-dir',str(a.run_dir),'--out',str(accept)];r=subprocess.run(cmd,capture_output=True,text=True);need(r.returncode==0 and accept.exists(),'valid run rejected:'+label)
 cases={}
 q=copy.deepcopy(j);q['status']='RUNNING';cases['incomplete']=json.dumps(q)
 q=copy.deepcopy(j);q['modules'][0]['source_sha256']='0'*64;cases['source']=json.dumps(q)
 q=copy.deepcopy(j);q['modules'][0]['object_sha256']='0'*64;cases['object']=json.dumps(q)
 q=copy.deepcopy(j);q['modules'][0]['dependency_probe']='/tmp/not-an-admitted-object.olean\n';cases['dependency']=json.dumps(q)
 q=copy.deepcopy(j);q['modules']=q['modules'][:-1];cases['missing-module']=json.dumps(q)
 q=copy.deepcopy(j);q['whole_pipeline_source_first_PV']=True;cases['false-PV']=json.dumps(q)
 q=copy.deepcopy(j);q['li_definition_hypotheses']=['assumed series'];cases['extra-premise']=json.dumps(q)
 cases['duplicate-key']='{"schema":"a","schema":"b"}'
 cases['nonfinite']='{"x":NaN}'
 for tag,data in cases.items():
  bad=O/(label+'-'+tag+'.json');bad.write_text(data);out=O/(label+'-'+tag+'-must-not-exist.json');c=prefix+[str(S/'verify_strong.py'),'--run-dir',str(a.run_dir),'--receipt',str(bad),'--out',str(out)];z=subprocess.run(c,capture_output=True,text=True);need(z.returncode!=0 and not out.exists(),'invalid case accepted:'+label+':'+tag)
 for args in [[],['--wrong-option']]:
  z=subprocess.run(prefix+[str(S/'verify_strong.py'),*args],capture_output=True,text=True);need(z.returncode!=0,'invalid CLI accepted')
 z=subprocess.run(prefix+[str(S/'reproduce.py'),'--check'],capture_output=True,text=True);need(z.returncode==0,'source layout check failed:'+label)
 rows.append({'mode':label,'accepted':True,'invalid_mutations_rejected':len(cases),'invalid_CLIs_rejected':2,'source_layout_check':True})
record={'status':'PASS_NORMAL_O_OO_ACTUAL_CLI_POSITIVE_AND_NEGATIVE_CONTROLS','rows':rows,'validator_sha256':hashlib.sha256((S/'verify_strong.py').read_bytes()).hexdigest(),'controller_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'negative_controls_do_not_replace_recompilation':True};tmp=O/'RESULT.pending';tmp.write_text(json.dumps(record,indent=2)+'\n');os.replace(tmp,O/'RESULT.json');print(json.dumps(record))
