from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,time,datetime
S=Path(__file__).resolve().parents[1]
SCRIPT=S/'scripts/resume_profiled_source_closure.py'
D=Path(sys.argv[1]).resolve()
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
need(not D.exists(),'fresh controls root');D.mkdir()
context=json.loads((S/'BUILD_CONTEXT.json').read_text());compiler=Path(context['compiler']);need(sha(compiler)==context['compiler_sha256'],'compiler')
profile={'exact':{'ProfileFixture.HeavyA':192,'ProfileFixture.HeavyB':96},'prefix':{}}
(D/'PROFILE.json').write_text(json.dumps(profile)+'\n');bad={'exact':{'ProfileFixture.HeavyA':301},'prefix':{}};(D/'BAD_PROFILE.json').write_text(json.dumps(bad)+'\n')
records=[]
def fixture(label):
 root=D/label;root.mkdir();source=root/'source';(source/'ProfileFixture').mkdir(parents=True);objects=root/'lean';(objects/'ProfileFixture').mkdir(parents=True);modules=[]
 bodies={'Seed':('','theorem seed : True := True.intro'), 'HeavyA':('import ProfileFixture.Seed\n','theorem heavyA : True := seed'),'HeavyB':('import ProfileFixture.Seed\n','theorem heavyB : 1=1 := rfl'),'Normal':('import ProfileFixture.Seed\n','theorem normal : 2=2 := rfl'),'After':('import ProfileFixture.HeavyA\nimport ProfileFixture.HeavyB\nimport ProfileFixture.Normal\n','theorem after : True := heavyA')}
 for name,(imports,body) in bodies.items():
  f=source/'ProfileFixture'/(name+'.lean');f.write_text(imports+'namespace ProfileFixture\n'+body+'\nend ProfileFixture\n');dependencies=re.findall(r'^import (.*)$',imports,re.M)
  modules.append({'module':'ProfileFixture.'+name,'root':str(source),'source':str(f),'source_sha256':sha(f),'imports':dependencies})
 plan={'targets':['ProfileFixture.After'],'selected_theorems':['ProfileFixture.after'],'modules':modules,'compiler':str(compiler),'compiler_sha256':sha(compiler),'context':str(S/'BUILD_CONTEXT.json'),'context_sha256':sha(S/'BUILD_CONTEXT.json'),'generic_libraries':context['generic_libraries'],'old_application_objects_used':False,'payloads':[],'memory_ceiling_bytes':48<<30}
 (root/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n');seed=modules[0];leaf=root/'audit'/seed['module'];leaf.mkdir(parents=True);(leaf/'source.lean').write_bytes(Path(seed['source']).read_bytes());obj=objects/'ProfileFixture/Seed.olean';cmd=[str(compiler),'-j1','-R',str(source),seed['source'],'-o',str(obj)];env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(objects),*context['generic_libraries']]))
 started=time.monotonic()
 with(leaf/'stdout').open('w')as so,(leaf/'stderr').open('w')as se:r=subprocess.run(['/usr/bin/time','-v','-o',str(leaf/'rusage'),*cmd],env=env,cwd=source,stdout=so,stderr=se)
 need(r.returncode==0,'real prerequisite kernel compile');rss=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',(leaf/'rusage').read_text())[1])*1024
 receipt={'module':seed['module'],'source':seed['source'],'source_sha256':seed['source_sha256'],'source_unchanged_during_compile':True,'command':cmd,'exit_code':0,'seconds':time.monotonic()-started,'peak_rss_bytes':rss,'oom_or_sigkill_event':False}
 for field,path in [('object',obj),('stdout',leaf/'stdout'),('stderr',leaf/'stderr'),('rusage',leaf/'rusage')]:receipt[field]=str(path);receipt[field+'_sha256']=sha(path)
 (leaf/'RUN.json').write_text(json.dumps(receipt,indent=2)+'\n');return root

def invoke(mode,case,cmd,want):
 route=D/(mode+'-'+case);route.mkdir();r=subprocess.run(cmd,capture_output=True,text=True);(route/'stdout').write_text(r.stdout);(route/'stderr').write_text(r.stderr)
 need((r.returncode==0)==want,'CLI control '+mode+' '+case+' '+r.stderr[-1500:]+r.stdout[-1500:]);records.append({'mode':mode,'case':case,'command':cmd,'exit_code':r.returncode,'stdout_sha256':sha(route/'stdout'),'stderr_sha256':sha(route/'stderr')});return r
for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
 base=[sys.executable,*flags,str(SCRIPT)];root=fixture(mode+'-good-fixture');out=root/'resume-profiled-test'
 args=['--run-root',str(root),'--out',str(out),'--jobs','4','--cpus','8,9,10,11','--memory-gib','48','--aggregate-gib','300','--host-reserve-gib','512','--profile-json',str(D/'PROFILE.json')]
 preview_args=args.copy();preview_args[preview_args.index('--out')+1]=str(root/'resume-profiled-preview')
 invoke(mode,'readback-only',base+preview_args+['--readback-only'],True)
 invoke(mode,'fresh-weighted',base+args,True);invoke(mode,'readback-complete',base+['--check',str(out)],True)
 result=json.loads((out/'RESULT.json').read_text());need(result['resumed_count']==1 and len(result['records'])==6,'all and only fixture sources plus final audit')
 schedule=[json.loads(line)for line in(out/'SCHEDULE.jsonl').read_text().splitlines()];need(max(e['running_caps_after_bytes']for e in schedule)==288<<30,'actual weighted288GiB overlap/300ceiling')
 for name,cap in [('ProfileFixture.HeavyA',192),('ProfileFixture.HeavyB',96),('ProfileFixture.Normal',48)]:
  row=next(r for r in result['records']if r['module']==name);need(row['worker_memory_ceiling_bytes']==cap<<30 and row['observed_process_limits']is not None,'actual inherited per-module cap observation')
 badroot=fixture(mode+'-negative-fixture');badargs=['--run-root',str(badroot),'--out',str(badroot/'resume-profiled-bad'),'--jobs','4','--cpus','8,9,10,11']
 invoke(mode,'reject-aggregate301',base+badargs+['--aggregate-gib','301'],False)
 invoke(mode,'reject-profile301',base+badargs+['--profile-json',str(D/'BAD_PROFILE.json')],False)
 log=badroot/'audit/ProfileFixture.Seed/stdout';log.write_text(log.read_text()+'UNACCEPTED TAMPERING\n');invoke(mode,'reject-reused-artifact',base+badargs,False)
 copied=root/'rejected-journal-copy';shutil.copytree(out,copied);journal=copied/'SCHEDULE.jsonl';events=journal.read_text().splitlines();first=json.loads(events[0]);first['running_caps_after_bytes']+=1;events[0]=json.dumps(first);journal.write_text('\n'.join(events)+'\n');invoke(mode,'reject-weight-journal',base+['--check',str(copied)],False)
result={'status':'PASS_PROFILED_RESUME_ACTUAL_NORMAL_O_OO_WEIGHTED_RESOURCE_AND_READBACK_CONTROLS','controller_sha256':sha(SCRIPT),'harness_sha256':sha(Path(__file__)),'controller':str(SCRIPT),'routes':records,'fixtures_are_synthetic_not_research_outcomes':True,'all_fresh_routes_real_Lean_compilation':True,'observed_process_caps_gib':[192,96,48],'maximum_actual_reserved_gib':288,'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'routes':len(records),'result':str(D/'RESULT.json'),'controller_sha256':sha(SCRIPT)}))
