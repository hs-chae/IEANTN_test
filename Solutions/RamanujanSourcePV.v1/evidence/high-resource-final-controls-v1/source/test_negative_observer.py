from pathlib import Path
import hashlib,json,subprocess,sys,time
D=Path('/data/ivy-ramanujan-source-pv-20261119/high-observer-controls-v1');S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1');W=S/'scripts/run_observed_high_campaign.py';C=S/'scripts/execute_demand_high_resource.py';O=D/'negative-controls';O.mkdir(exist_ok=False)
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]
for mode in ['Normal','O','OO']:
 flags=[]if mode=='Normal'else['-'+mode];original=json.loads((D/('command-'+mode+'.json')).read_text())
 for name,hashbad,modebad,cmd in [('wrong-hash',True,False,original),('mode-mismatch',False,True,original),('unapproved-research',False,False,[x for x in original if x!='--control']),('wrong-executable',False,False,['/bin/false']+original[1:])]:
  source=O/(mode+'-'+name+'.json');source.write_text(json.dumps(cmd));cmd=[sys.executable]+flags+[str(W),'--command-json',str(source),'--controller-sha256','0'*64 if hashbad else sha(C),'--out',str(O/(mode+'-'+name)),'--path',str(D)]
  if name!='unapproved-research'and not modebad:cmd+=['--control']
  p=subprocess.run(cmd,capture_output=True,text=True);need(p.returncode!=0,'must reject '+mode+name);need(not(O/(mode+'-'+name)).exists(),'reject before observer/controller launch');(O/(mode+'-'+name+'.stderr')).write_text(p.stderr);rows.append(dict(mode=mode,name=name,command=cmd,returncode=p.returncode,stderr_sha256=sha(O/(mode+'-'+name+'.stderr'))))
r=dict(status='PASS_OBSERVER_WRAPPER_NEGATIVE_ALL_OPTIMIZATIONS',wrapper_sha256=sha(W),observer_sha256=sha(S/'scripts/observe_high_campaign.py'),controller_sha256=sha(C),routes=rows);(O/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],routes=len(rows))))
