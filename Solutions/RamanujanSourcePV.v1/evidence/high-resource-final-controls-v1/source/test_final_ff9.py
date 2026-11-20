from pathlib import Path
import hashlib,json,subprocess,sys,time
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1');D=Path('/data/ivy-ramanujan-source-pv-20261119/high-budget-controller-controls-v1');C=S/'scripts/execute_demand_high_resource.py';EXPECTED='ff9f23a4832c105e368f7cfe3c5ae400dbd5e4cec32c04a4c2135ea972d5ef63';O=D/'final-controls-ff9';O.mkdir(exist_ok=False)
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
need(sha(C)==EXPECTED,'frozen current controller')
rows=[]
def run(mode,name,args,good):
 cmd=[sys.executable]+([]if mode=='Normal'else['-'+mode])+[str(C)]+list(map(str,args));t=time.monotonic();p=subprocess.run(cmd,capture_output=True,text=True);base=O/(mode+'-'+name);base.with_suffix('.stdout').write_text(p.stdout);base.with_suffix('.stderr').write_text(p.stderr);need((p.returncode==0)==good,mode+' '+name+' expected '+str(good)+' got '+str(p.returncode)+' '+p.stderr[-150:]);rows.append(dict(mode=mode,name=name,command=cmd,returncode=p.returncode,seconds=time.monotonic()-t,expected_acceptance=good,stdout_sha256=sha(base.with_suffix('.stdout')),stderr_sha256=sha(base.with_suffix('.stderr'))))
for mode in ['Normal','O','OO']:
 result=D/('final-run-'+mode)/'RESULT.json';need(result.is_file(),'all actual end-to-end runs complete');r=json.loads(result.read_text());need(r['configuration']['controller_sha256']==EXPECTED and r['completed']==18 and r['imported_successes']==4,'exact completed fresh child and imported paths');need(r['configuration']['python_optimization']==dict(Normal=0,O=1,OO=2)[mode],'actual parent optimization');
 for item in r['records']:
  if not item['reused']:
   child=json.loads(Path(item['observation']).read_text())['command'];need((('-'+mode)in child)if mode!='Normal'else not any(v in child for v in ['-O','-OO']),'actual child optimization propagation')
 run(mode,'valid-readback',['--check',result],True)
 base=['--control','--manifest',D/('proposal-'+mode)/'PROPOSAL.json','--out',O/(mode+'-never-dispatched'),'--expected-pi','1000=168','--expected-pi','367=73','--import-audit',D/('data-'+mode)/'audit']
 for name,extra in [('per-run301',['--memory-gib','301']),('aggregate769',['--aggregate-gib','769']),('duplicate-cpus',['--cpus','112,112,114,115,116,117,118,119']),('wrong-import-count',['--expected-import-count','5']),('scratch-forecast300',['--scratch-estimate-gib','300']),('wrong-owned-root',['--owned-scratch-root',D])]:run(mode,name,base+extra,False)
 for name,text in [('duplicate-json','{"status":1,"status":2}'),('nan-json','{"status":NaN}'),('infinite-json','{"status":1e999}')]:
  bad=O/(mode+'-'+name+'.json');bad.write_text(text);run(mode,name,['--check',bad],False)
 for name,change in [('partial-status',lambda v:v.update(status='DRAINED_CHECKPOINT_NOT_ACCEPTANCE')),('missing-module',lambda v:v['records'].pop()),('wrong-object-proof',lambda v:v['records'][0]['proof'].update(object_sha256='0'*64))]:
  v=json.loads(result.read_text());change(v);bad=O/(mode+'-'+name+'.json');bad.write_text(json.dumps(v));run(mode,name,['--check',bad],False)
 v=json.loads(result.read_text());j=O/(mode+'-halved-journal.jsonl');events=[json.loads(x)for x in Path(v['journal']).read_text().splitlines()]
 for e in events:e['cap_bytes']//=2;e['reserved_bytes']//=2
 j.write_text(''.join(json.dumps(e)+'\n'for e in events));v.update(journal=str(j),journal_sha256=sha(j),peak_reserved_bytes=v['peak_reserved_bytes']//2);bad=O/(mode+'-halved-journal.json');bad.write_text(json.dumps(v));run(mode,'self-consistent-halved-journal',['--check',bad],False)
 v=json.loads(result.read_text());obs=json.loads(Path(v['final_audit']['observation']).read_text());obs['memory_limit_bytes']//=2;op=O/(mode+'-bad-auditor-observation.json');op.write_text(json.dumps(obs));v['final_audit'].update(observation=str(op),observation_sha256=sha(op));bad=O/(mode+'-bad-auditor-cap.json');bad.write_text(json.dumps(v));run(mode,'wrong-auditor-cap',['--check',bad],False)
 proposal=json.loads((D/('proposal-'+mode)/'PROPOSAL.json').read_text())
 for name,mut in [('source-hash',lambda v:v['modules'][0].update(sha256='0'*64)),('packed-hash',lambda v:v.update(packed_sha256='0'*64)),('boolean-records',lambda v:v.update(records=True))]:
  v=json.loads(json.dumps(proposal));mut(v);bad=O/(mode+'-'+name+'-manifest.json');bad.write_text(json.dumps(v));args=base.copy();args[args.index('--manifest')+1]=bad;run(mode,name,args,False)
need(sha(C)==EXPECTED,'unchanged final code');result=dict(status='PASS_HIGH_RESOURCE_CURRENT_BYTE_ALL_OPTIMIZATION_CONTROLS',controller=str(C),controller_sha256=EXPECTED,actual_final_runs=[dict(path=str(D/('final-run-'+m)/'RESULT.json'),sha256=sha(D/('final-run-'+m)/'RESULT.json'))for m in ['Normal','O','OO']],routes=rows,route_count=len(rows),qualification='Tiny actual kernel proofs exercise compilation, import, final exact type/root/axiom audit and resource reservations; no original high research pool launched. These controls do not prove arbitrary programs or numerical claims.');temp=O/'RESULT.pending';temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(O/'RESULT.json');print(json.dumps(dict(status=result['status'],routes=len(rows),receipt=str(O/'RESULT.json'),sha256=sha(O/'RESULT.json'))))
