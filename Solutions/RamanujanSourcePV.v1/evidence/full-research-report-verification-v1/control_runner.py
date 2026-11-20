#!/usr/bin/env python3
from pathlib import Path
import argparse,subprocess,json,hashlib,shutil
p=argparse.ArgumentParser();p.add_argument('--solution',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();s=a.solution.resolve();o=a.out.resolve();o.mkdir(exist_ok=False);script=s/'scripts/render_full_research_checkpoint.py';shutil.copyfile(script,o/'renderer.py')
base=(s/'evidence/RESEARCH_CHECKPOINT_STATUS_20261120.json').read_text();cases={'valid':base,'duplicate':base.replace('"full_threshold_proof_closed": false','"full_threshold_proof_closed": true, "full_threshold_proof_closed": false'),'infinite':base[:-2]+', "extra": 1e999\n}','nan':base[:-2]+', "extra": NaN\n}','global-success':base.replace('"full_threshold_proof_closed": false','"full_threshold_proof_closed": true')};rows=[];valid=[]
for mode in [[],['-O'],['-OO']]:
 for case,raw in cases.items():
  name=(mode[0][1:]if mode else'normal')+'-'+case;inp=o/(name+'.json');inp.write_text(raw);out=o/(name+'.html');cmd=['python3',*mode,str(script),'--status',str(inp),'--out',str(out)];v=subprocess.run(cmd,capture_output=True,text=True);(o/(name+'.stdout')).write_text(v.stdout);(o/(name+'.stderr')).write_text(v.stderr)
  if (v.returncode==0)!=(case=='valid')or(case!='valid'and out.exists()):raise ValueError((name,v.returncode))
  if case=='valid':valid.append(hashlib.sha256(out.read_bytes()).hexdigest())
  rows.append(dict(name=name,command=cmd,returncode=v.returncode,accepted=case=='valid'))
if len(set(valid))!=1:raise ValueError('mode output differs')
j=dict(status='PASS15_ACTUAL_RENDERER_ROUTES_NORMAL_O_OO',renderer_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),report_sha256=valid[0],cases=rows);(o/'RESULT.json').write_text(json.dumps(j,indent=2)+'\n');print(j['status'],valid[0])
