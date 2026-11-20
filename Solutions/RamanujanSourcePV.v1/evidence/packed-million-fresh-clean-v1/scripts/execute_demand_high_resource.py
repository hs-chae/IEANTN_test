#!/usr/bin/env python3
"""Reviewed-plan, weighted high-resource kernel certificate replay; not C PV.

The immutable manifest is complete only after every source compilation and a
fresh exact-type/axiom audit. Progress, imported ledgers and numerical proposals
are never accepted as proof. Existing controllers and their receipts are reused
only through independent exact source/object/log readback.
"""
from pathlib import Path
import argparse,datetime,json,math,os,re,shutil,signal,subprocess,sys,time
from execute_demand_manifest_parallel import need,sha,read,publish,STD3
S=Path(__file__).resolve().parents[1]
G=1024**3
HIGH='RamanujanPV.HighTransitionCount'
HIGH_LOCK=S/'evidence/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json'
HIGH_LOCK_SHA='7f5a1641e363a4530cf7414b893b11f9cc1cf4b3fc830b89dd7019e96a9a883e'
PYTHON=[sys.executable]+(['-OO']if sys.flags.optimize>=2 else['-O']if sys.flags.optimize else[])

def strict_text(text):
    def pairs(items):
        result={}
        for key,value in items:need(key not in result,'duplicate JSON key');result[key]=value
        return result
    def finite(text):
        value=float(text);need(math.isfinite(value),'finite JSON number');return value
    return json.loads(text,object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))

def read(path):return strict_text(Path(path).read_text())

def available():
    return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024

class DiskMeter:
    """Actual owned allocated bytes; no symlink traversal or deletion."""
    def __init__(self,root,forecast=0):self.root=Path(root);self.forecast=forecast;self.last=None;self.peak=0
    def measure(self,force=False):
        if not force and self.last is not None and time.time()-self.last['measured_unix']<5:return self.last
        try:
            run=subprocess.run(['du','-s','-B1','-x',str(self.root)],capture_output=True,text=True,timeout=50);need(run.returncode==0,'owned scratch measurement');match=re.fullmatch(r'([0-9]+)\s+[^\n]+\n?',run.stdout);need(match is not None,'strict owned scratch byte count');used=int(match[1]);self.peak=max(self.peak,used);self.last=dict(root=str(self.root),allocated_bytes=used,forecast_bytes=self.forecast,free_bytes=shutil.disk_usage(self.root).free,measured_unix=time.time(),max_measurement_age_seconds=5,error=None)
        except Exception as error:self.last=dict(root=str(self.root),allocated_bytes=None,free_bytes=shutil.disk_usage(self.root).free,measured_unix=time.time(),error=repr(error))
        return self.last
    def okay(self,row):return row['error']is None and row['free_bytes']>=1024*G and row['allocated_bytes']+self.forecast<=300*G

def imported_records(study,trees):
    records={}
    for tree in trees:
        tree=tree.resolve();need(tree.is_relative_to(study.scratch)and tree.is_dir(),'owned existing imported audit tree')
        for path in sorted(tree.rglob('RUN.json')):
            row=read(path);name=row.get('module')
            if name in study.by and row.get('status')=='COMPILED':
                proof=study.audit(name,path)
                if name in records:need(records[name]['proof']['object_sha256']==proof['object_sha256'],'consistent exact successful imported object')
                else:records[name]=dict(module=name,compiler_receipt=str(path),proof=proof,reused=True,observation=None)
    for name in records:need((set(study.by[name]['dependencies'])&set(study.names))<=set(records),'complete imported generated dependencies')
    return records

def snapshot(pid):
    try:
        base=Path('/proc')/str(pid);stat=(base/'stat').read_text();fields=stat[stat.rfind(')')+2:].split();status=(base/'status').read_text();limits=(base/'limits').read_text();limit=re.search(r'^Max address space\s+(\S+)\s+(\S+)\s+',limits,re.M)
        return dict(pid=pid,start_token=fields[19],affinity=sorted(os.sched_getaffinity(pid)),command=(base/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace').strip(),vmpeak_bytes=int(re.search(r'^VmPeak:\s*(\d+)',status,re.M)[1])*1024 if 'VmPeak:' in status else None,rss_bytes=int(re.search(r'^VmRSS:\s*(\d+)',status,re.M)[1])*1024 if 'VmRSS:' in status else None,rlimit_as_soft=limit[1]if limit else None,rlimit_as_hard=limit[2]if limit else None)
    except (FileNotFoundError,ProcessLookupError,PermissionError):return None

def descendants(pid):
    result=[]
    def visit(p):
        s=snapshot(p)
        if s is None:return
        result.append(s)
        try:children=(Path('/proc')/str(p)/'task'/str(p)/'children').read_text().split()
        except (FileNotFoundError,ProcessLookupError,PermissionError):children=[]
        for child in children:visit(int(child))
    visit(pid);return result

class Study:
    def __init__(self,manifest,context,expected,control=False):
        self.manifest=Path(manifest).resolve();self.d=read(self.manifest);self.context=Path(context).resolve();need(self.context==(S/'BUILD_CONTEXT.json').resolve(),'compile helper uses exact pinned project context');self.c=read(self.context);self.compiler=Path(self.c['compiler']);need(sha(self.compiler)==self.c['compiler_sha256'],'exact pinned compiler');self.compiler_hash=sha(self.compiler);self.context_hash=sha(self.context);self.objects=Path(self.c['new_application_object_root']).resolve();self.scratch=self.objects.parent;self.root=Path(self.d['source_root']).resolve();d=self.d
        need(d['schema']=='RAMANUJAN_PACKED_DEMAND_CERTIFICATE_PROPOSAL_V1'and d['status']=='UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_CHECKS','exact immutable proposal status');need(all(type(d[key])is int and d[key]>0 for key in ['records','data_chunk','proof_chunk','packed_bits','packed_bytes_per_record','packed_bytes'])and all(type(n)is int and n>=0 for n in d['queries'])and all(type(row['N'])is int and type(row['value'])is int and row['N']>=0 and row['value']>=0 for row in d['results']),'strict original scientific integer parameters');need(self.root.is_relative_to(self.scratch)and self.root!=self.scratch,'owned original sources');self.names=[x['module']for x in d['modules']];need(len(self.names)==len(set(self.names)),'unique module compiler identities');self.by={x['module']:x for x in d['modules']};paths=[Path(x['source']).resolve()for x in d['modules']];need(len(paths)==len(set(paths))and sorted(paths)==sorted(x.resolve()for x in self.root.rglob('*.lean')),'complete source-file population')
        for m,p in zip(d['modules'],paths):
            need(p.is_file()and p.is_relative_to(self.root)and not p.is_symlink()and sha(p)==m['sha256'],'exact written source '+m['module']);need(m['kind']in['data','check','final'],'known kind');need(isinstance(m['dependencies'],list)and len(m['dependencies'])==len(set(m['dependencies'])),'unique dependency identities')
        self.expected=[tuple(x)for x in expected];need(len(self.expected)==len(set(n for n,v in self.expected))and all(type(n)is int and type(v)is int and n>=0 and v>=0 for n,v in self.expected),'unique exact integer locked queries');need(d['queries']==[n for n,v in self.expected]and [(r['N'],r['value'])for r in d['results']]==self.expected,'exact independently supplied queries and counts');need(sha(d['packed_file'])==d['packed_sha256'],'every original packed-data byte');need(Path(d['packed_file']).stat().st_size==d['packed_bytes']==d['records']*41 and d['packed_bits']==324 and d['packed_bytes_per_record']==41,'exact original word layout');need(d['packed_widths']==[2,22,42,42,32,32,32,32,22,22,22,22],'all original twelve fields')
        self.scientific={str(S/'RamanujanPV'/n):sha(S/'RamanujanPV'/n)for n in['QuotientCertificateCode.lean','QuotientDemandCheck.lean','QuotientPartition.lean']};ns=d['namespace'];need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*',ns)is not None,'safe compiler namespace');self.raw=[ns+'.Data'+format(i,'04d')for i in range((d['records']+d['data_chunk']-1)//d['data_chunk'])];self.checks=[ns+'.Check'+format(i,'04d')for i in range((d['records']+d['proof_chunk']-1)//d['proof_chunk'])];need(set(self.names)==set(self.raw+[ns+'.Gaps',ns+'.Data',ns+'.GapCheck',ns+'.Final']+self.checks),'exact full raw/gaps/data/check/final universe');need(d['final_module']==ns+'.Final','exact final compiler identity')
        if not control:need(ns==HIGH and self.expected==[(1490000000000,55206486339)]and d['records']==90670946 and len(self.raw)==692 and len(self.checks)==2768 and len(self.names)==3464,'fixed owner high-count universe and value')
        else:need(ns!=HIGH,'control mode cannot weaken real high-run universe')
        for result in d['results']:need(type(result['index'])is int and 0<=result['index']<d['records']and len(result['entry'])==12 and all(type(v)is int and v>=0 for v in result['entry'])and result['entry'][0]==2 and result['entry'][2:4]==[result['N'],result['value']],'every original full twelve-field root literal')
        if not control:
            need(sha(HIGH_LOCK)==HIGH_LOCK_SHA,'published original high-source identity lock');lock=read(HIGH_LOCK);need(lock['schema']=='ieantn.ramanujan.high-original-proposal-identities.v1'and lock['modules']=={x['module']:x['sha256']for x in d['modules']}and lock['original_candidates_unverified']==d['results'],'complete published original module map and root literals')
            for key in ['namespace','queries','records','packed_sha256','packed_bits','data_chunk','proof_chunk','generator_sha256']:need(lock[key]==d[key],'published original field '+key)
        for name in self.names:
            expected_kind='check'if name in self.checks or name==ns+'.GapCheck'else('final'if name==d['final_module']else'data');need(self.by[name]['kind']==expected_kind,'exact module role '+name)
    def mandatory(self,name):
        if name==self.d['final_module']:return ['pi_'+str(n)for n,v in self.expected]
        if name.endswith('.GapCheck'):return ['gaps_checked']
        if name in self.checks:return ['part_'+name[-4:]]
        return []
    def reports(self,text,required,numeric=False):
        found={}
        for full in required:
            no=re.search(r"'"+re.escape(full)+r"' does not depend on any axioms",text);ax=re.search(r"'"+re.escape(full)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S);need(no is not None or ax is not None,'actual named dependency report '+full);axioms=[]if no else[v.strip()for v in ax[1].split(',')if v.strip()];need(set(axioms)<=STD3 and(not numeric or not axioms),'exact theorem trust boundary '+full);found[full]=axioms
        return found
    def audit(self,name,path):
        m=self.by[name];path=Path(path).resolve();need(path.is_relative_to(self.scratch),'owned receipt');r=read(path);folder=path.parent;need(r['status']=='COMPILED'and r['returncode']==0 and r['module']==name and r['source_sha256']==m['sha256']and r['source_unchanged_during_compile']is True and r['compiler_sha256']==self.compiler_hash and r['generic_dependency_context_sha256']==self.context_hash,'actual source/compiler/context '+name);need(Path(r['source']).resolve()==Path(m['source']).resolve(),'exact manifest receipt source path');need(sha(folder/'source.lean')==m['sha256']==sha(m['source']),'complete exact source snapshot')
        for f,k in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(folder/f)==r[k],'actual log '+name)
        text=(folder/'stdout').read_text();errors=(folder/'stderr').read_text();need(not any(v in text+errors for v in['sorryAx','Lean.ofReduceBool','declaration uses `sorry`']),'forbidden execution/proof axiom '+name);requested=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)',Path(m['source']).read_text(),re.M);mandatory=self.mandatory(name);need(set(mandatory)<=set(requested),'all compulsory printed facts '+name);symbols=[x if '.'in x else self.d['namespace']+'.'+x for x in sorted(set(requested)|set(mandatory))];axioms=self.reports(text,symbols,m['kind']=='check');obj=self.objects/Path(*name.split('.')).with_suffix('.olean');need(obj.is_file()and sha(obj)==r['object_sha256'],'exact proof object '+name);need(all(sha(p)==h for p,h in self.scientific.items()),'unchanged scientific semantics');usage=(folder/'rusage.txt').read_text();peak=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',usage);need(peak is not None,'actual rusage');need(type(r['memory_limit_bytes'])is int and 0<r['memory_limit_bytes']<=300*G,'actual bounded individual limit');need(r['command']==['/usr/bin/time','-v','-o',str(folder/'rusage.txt'),str(self.compiler),'-j1','-R',str(self.root),str(Path(m['source']).resolve()),'-o',str(obj)],'exact original compiler -R/source/-o command')
        return dict(module=name,compiler_receipt=str(path),compiler_receipt_sha256=sha(path),source_sha256=m['sha256'],object=str(obj),object_sha256=sha(obj),seconds=r['elapsed_seconds'],peak_rss_bytes=int(peak[1])*1024,memory_limit_bytes=r['memory_limit_bytes'],affinity=r['affinity'],mandatory_axiom_reports=mandatory,axioms=axioms)
    def audit_text(self):
        ns=self.d['namespace'];lines=['import '+self.d['final_module'],'open RamanujanPV.QuotientDemandCheck']
        for name in [ns+'.GapCheck']+self.checks:
            if name.endswith('.GapCheck'):symbol=ns+'.gaps_checked';statement='checkGaps '+ns+'.gaps '+ns+'.gapCount = true'
            else:
                chunk=int(name[-4:]);start=chunk*self.d['proof_chunk'];size=min(self.d['proof_chunk'],self.d['records']-start);need(size>0,'complete exact chunk range');symbol=ns+'.part_'+name[-4:];statement='allFrom (checkEntry '+ns+'.nodes '+ns+'.gaps '+ns+'.gapCount) '+str(start)+' '+str(size)+' = true'
            lines+=['example : '+statement+' := '+symbol,'#print axioms '+symbol]
        lines+=['example : checkEntries '+ns+'.nodes '+ns+'.gaps '+ns+'.gapCount '+str(self.d['records'])+' = true := '+ns+'.entries_checked','#print axioms '+ns+'.entries_checked']
        for result in self.d['results']:
            symbol=ns+'.root_'+str(result['N']);literal='⟨'+','.join(str(v)for v in result['entry'])+'⟩';lines+=['example : '+ns+'.nodes.get '+str(result['index'])+' = '+literal+' := '+symbol,'#print axioms '+symbol]
        for n,v in self.expected:lines+=['example : _root_.Nat.primeCounting '+str(n)+' = '+str(v)+' := '+ns+'.pi_'+str(n),'#print axioms '+ns+'.pi_'+str(n)]
        return '\n'.join(lines)+'\n'

def configuration(a,study,cpus):
    return dict(manifest=str(study.manifest),manifest_sha256=sha(study.manifest),context=str(study.context),context_sha256=study.context_hash,compiler_sha256=study.compiler_hash,controller_sha256=sha(__file__),compiler_helper_sha256=sha(S/'scripts/compile_lean.py'),validation_helper_sha256=sha(S/'scripts/execute_demand_manifest_parallel.py'),scientific_source_sha256=study.scientific,packed_sha256=study.d['packed_sha256'],expected_pi=study.expected,total=len(study.names),jobs=a.jobs,cpus=cpus,memory_gib=a.memory_gib,aggregate_gib=a.aggregate_gib,gap_memory_gib=a.gap_memory_gib,final_memory_gib=a.final_memory_gib,host_reserve_gib=512,min_available_gib=1024,control=a.control,stage=a.stage,expected_import_count=a.expected_import_count,owned_scratch_root=str(study.scratch),min_disk_free_gib=1024,max_owned_scratch_gib=300,estimated_new_scratch_gib=a.scratch_estimate_gib,disk_poll_measurement_max_age_seconds=5,python_optimization=sys.flags.optimize,original_high_identity_lock_sha256=HIGH_LOCK_SHA if not a.control else None,import_audit=[str(x.resolve())for x in a.import_audit],plan_version='HIGH_DEMAND_WEIGHTED_V1')

def validate_journal(path,aggregate,expected_caps=None,expected_scratch_root=None,expected_scratch_forecast=None):
    reserved={};reservation_events={};started=set();all_started=set();maximum=0;seen=set()
    for line in Path(path).read_text().splitlines():
        event=strict_text(line);kind=event['event'];need(type(event['reserved_bytes'])is int and event['reserved_bytes']>=0 and type(event['cap_bytes'])is int and event['cap_bytes']>=0 and type(event['host_memavailable_bytes'])is int and event['host_memavailable_bytes']>=0,'strict journal integer limits')
        if kind in ['reserve','release','started']:
            name=event['module'];cap=event['cap_bytes'];need(isinstance(name,str)and 0<cap<=300*G,'actual bounded reservation identity')
            if expected_caps is not None:need(name in expected_caps and cap==expected_caps[name],'reservation linked to actual compiler role/receipt/observation cap')
            if kind=='reserve':need(name not in reserved,'unique live reservation');reserved[name]=cap;reservation_events[name]=event;seen.add(name)
            elif kind=='started':
                need(reserved.get(name)==cap and name not in started,'start follows exact live reservation');before=reservation_events[name];need(before['host_memavailable_bytes']>=max(1024*G,512*G+before['reserved_bytes']),'every actual dispatch had genuine1TiB and512GiB+reserved caps available');disk=before['disk'];need(disk['error']is None and type(disk['free_bytes'])is int and disk['free_bytes']>=1024*G and type(disk['allocated_bytes'])is int and type(disk['forecast_bytes'])is int and disk['forecast_bytes']>=0 and disk['allocated_bytes']+disk['forecast_bytes']<=300*G and 0<=before['time_unix']-disk['measured_unix']<=10,'every actual dispatch had independently sufficient disk and bounded owned scratch');
                if expected_scratch_root is not None:need(disk['root']==expected_scratch_root,'exact owned experiment scratch root')
                if expected_scratch_forecast is not None:need(disk['forecast_bytes']==expected_scratch_forecast,'same explicit forecast headroom at every dispatch')
                need(type(event['pid'])is int and event['pid']>0 and isinstance(event['start_token'],str)and event['start_token'].isdigit(),'actual launched process token');started.add(name);all_started.add(name)
            else:
                need(reserved.pop(name,None)==cap,'release exact live reservation')
                if name not in started:need(event.get('reason')in['resources_changed_before_dispatch','spawn_failed','start_observation_failed'],'unstarted reservation explicitly cancelled')
                started.discard(name);reservation_events.pop(name)
        need(sum(reserved.values())==event['reserved_bytes']and sum(reserved.values())<=aggregate,'independent exact weighted journal');maximum=max(maximum,sum(reserved.values()))
    need(not reserved and not started,'all actual children completed and reservations drained')
    if expected_caps is not None:need(seen==all_started==set(expected_caps),'every actual dispatched compiler/auditor linked to reservation and start')
    return maximum

def check_result(path):
    path=Path(path).resolve();r=read(path);need(r['status']=='COMPLETE_HIGH_RESOURCE_KERNEL_CERTIFICATE_NOT_SOURCE_PV','complete acceptance, never checkpoint');cfg=r['configuration'];need(type(cfg['jobs'])is int and 1<=cfg['jobs']<=32 and type(cfg['aggregate_gib'])is int and type(cfg['control'])is bool and cfg['stage']=='all' and all(type(cfg[k])is int and 1<=cfg[k]<=300 for k in ['memory_gib','gap_memory_gib','final_memory_gib'])and max(cfg['jobs']*cfg['memory_gib'],cfg['gap_memory_gib'],cfg['final_memory_gib'])<=cfg['aggregate_gib']<=768 and cfg['host_reserve_gib']==512 and cfg['min_available_gib']==1024,'complete fixed resource policy');need(sha(r['plan'])==r['plan_sha256']and read(r['plan'])['configuration']==cfg,'exact unchanged concrete plan');study=Study(cfg['manifest'],cfg['context'],cfg['expected_pi'],cfg['control']);need(cfg['controller_sha256']==sha(__file__)and cfg['compiler_helper_sha256']==sha(S/'scripts/compile_lean.py')and cfg['validation_helper_sha256']==sha(S/'scripts/execute_demand_manifest_parallel.py'),'current exact acceptance code');need(cfg['manifest_sha256']==sha(study.manifest)and cfg['context_sha256']==study.context_hash and cfg['compiler_sha256']==study.compiler_hash and cfg['scientific_source_sha256']==study.scientific,'exact scientific/compiler configuration');need(cfg['packed_sha256']==study.d['packed_sha256']and cfg['original_high_identity_lock_sha256']==(HIGH_LOCK_SHA if not cfg['control']else None),'exact published packed/source identity configuration');need(cfg['owned_scratch_root']==str(study.scratch)and cfg['min_disk_free_gib']==1024 and cfg['max_owned_scratch_gib']==300 and cfg['disk_poll_measurement_max_age_seconds']==5,'independent exact disk/scratch policy');need(r['completed']==cfg['total']==len(study.names)and len(r['records'])==len(study.names),'entire exact source universe');names=[]
    for item in r['records']:
        name=item['module'];need(type(item['reused'])is bool and (item.get('observation')is None)==item['reused'],'exact imported versus actual child execution route');need(name not in names and name in study.by,'complete unique result identity');names.append(name);actual=study.audit(name,item['compiler_receipt']);need(actual==item['proof'],'each receipt/object/log independently read back');need(sha(item['compiler_receipt'])==item['proof']['compiler_receipt_sha256'],'receipt identity')
        if item.get('observation')is not None:
            need(sha(item['observation'])==item['observation_sha256'],'actual process observations preserved');obs=read(item['observation']);need(obs['module']==name and obs['returncode']==0,'actual successful process identity');cap=cfg['gap_memory_gib']if name.endswith('.GapCheck')else(cfg['final_memory_gib']if name==study.d['final_module']else cfg['memory_gib']);need(obs['memory_limit_bytes']==item['proof']['memory_limit_bytes']==cap*G,'actual dispatched per-role limit');need(len(item['proof']['affinity'])==1 and item['proof']['affinity'][0]in cfg['cpus'],'actual configured affinity');need(obs['initial']['pid']>0 and obs['initial']['start_token'].isdigit(),'actual PID/start token');
            if not cfg['control']:need(any(x['command'].startswith(str(study.compiler)+' ')and x['rlimit_as_soft']==x['rlimit_as_hard']==str(cap*G)and x['affinity']==item['proof']['affinity']for x in obs['actual_processes']),'observed actual compiler RLIMIT_AS')
    need(set(names)==set(study.names),'every original module accepted');plan=read(r['plan']);reuse=read(plan['imported_readback']['path']);need(sha(plan['imported_readback']['path'])==plan['imported_readback']['sha256']and reuse['controller_sha256']==cfg['controller_sha256']and reuse['manifest_sha256']==cfg['manifest_sha256'],'original enumerated imported readback identity');old={item['module']:item for item in reuse['records']};retained={item['module']:item for item in r['records']if item['reused']};need(old==retained and len(old)==reuse['count']==plan['imported_readback']['count']==r['imported_successes'],'every original imported success preserved exactly');
    if cfg['expected_import_count']is not None:need(len(old)==cfg['expected_import_count'],'independently expected import count in final acceptance')
    need(sha(r['journal'])==r['journal_sha256'],'exact weighted journal');need(validate_journal(r['journal'],cfg['aggregate_gib']*G)==r['peak_reserved_bytes'],'weighted aggregate replay');audit=r['final_audit'];source=Path(audit['source']);need(source.read_text()==study.audit_text()and sha(source)==audit['source_sha256'],'independent exact original type obligations');receipt=read(audit['receipt']);folder=Path(audit['receipt']).parent;need(sha(audit['receipt'])==audit['receipt_sha256']and receipt['status']=='COMPILED'and receipt['returncode']==0 and receipt['source_sha256']==audit['source_sha256']and receipt['compiler_sha256']==study.compiler_hash and receipt['generic_dependency_context_sha256']==study.context_hash,'actual complete exact-type audit');need(Path(receipt['source']).resolve()==source.resolve()and receipt['command']==['/usr/bin/time','-v','-o',str(folder/'rusage.txt'),str(study.compiler),'-j1','-R',audit['source_root'],str(source),'-o',str(study.objects/Path(*audit['module'].split('.')).with_suffix('.olean'))],'exact independent audit compiler/source/object command');need(sha(folder/'source.lean')==audit['source_sha256']and receipt['memory_limit_bytes']==cfg['final_memory_gib']*G,'trusted audit snapshot/actual limit');need(sha(audit['observation'])==audit['observation_sha256'],'trusted audit actual processes');audit_obs=read(audit['observation']);need(audit_obs['module']==audit['module']and audit_obs['returncode']==0 and audit_obs['memory_limit_bytes']==cfg['final_memory_gib']*G,'actual successful final-auditor process');
    if not cfg['control']:need(any(x['command'].startswith(str(study.compiler)+' ')and x['rlimit_as_soft']==x['rlimit_as_hard']==str(cfg['final_memory_gib']*G)and x['affinity']==receipt['affinity']for x in audit_obs['actual_processes']),'observed actual final-auditor RLIMIT_AS')
    for f,k in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(folder/f)==receipt[k],'trusted audit log')
    obj=study.objects/Path(*audit['module'].split('.')).with_suffix('.olean');need(sha(obj)==receipt['object_sha256'],'trusted actual audit object');log=(folder/'stdout').read_text()
    for symbol in re.findall(r'^#print axioms ([A-Za-z0-9_.]+)',study.audit_text(),re.M):study.reports(log,[symbol],symbol.rsplit('.',1)[-1].startswith(('part_','gaps_checked','root_')))
    usage=(folder/'rusage.txt').read_text();match=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',usage);need(match is not None and audit['peak_rss_bytes']==int(match[1])*1024,'independent final auditor peak RSS');need(r['actual_peak_worker_rss_bytes']==max([item['proof']['peak_rss_bytes']for item in r['records']]+[audit['peak_rss_bytes']])and r['actual_aggregate_peak_RAM_measured']is False,'exact observed peak scope');expected_caps={item['module']:item['proof']['memory_limit_bytes']for item in r['records']if not item['reused']};expected_caps[audit['module']]=receipt['memory_limit_bytes'];need(validate_journal(r['journal'],cfg['aggregate_gib']*G,expected_caps,cfg['owned_scratch_root'],cfg['estimated_new_scratch_gib']*G)==r['peak_reserved_bytes'],'all reservations bound to actual compiler caps');need(r['prime_count_results']==study.d['results']and r['source_first_PV']is False,'exact accepted scope');return dict(status='COMPLETE_HIGH_RESOURCE_RESULT_READBACK_PASS',modules=len(names),expected_pi=study.expected,all_exact_check_ranges_and_final_pi_audited=True,result_sha256=sha(path))

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path);p.add_argument('--out',type=Path);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--jobs',type=int,default=8);p.add_argument('--memory-gib',type=int,default=96);p.add_argument('--aggregate-gib',type=int,default=768);p.add_argument('--gap-memory-gib',type=int,default=192);p.add_argument('--final-memory-gib',type=int,default=256);p.add_argument('--cpus',default='112,113,114,115,116,117,118,119');p.add_argument('--expected-pi',action='append',default=[]);p.add_argument('--import-audit',type=Path,action='append',default=[]);p.add_argument('--expected-import-count',type=int);p.add_argument('--owned-scratch-root',type=Path);p.add_argument('--scratch-estimate-gib',type=int,default=8);p.add_argument('--stage',choices=['all','data','checks'],default='all');p.add_argument('--control',action='store_true');p.add_argument('--plan-only',action='store_true');p.add_argument('--approved-plan',type=Path);p.add_argument('--check',type=Path);a=p.parse_args()
    if a.check is not None:need(a.manifest is None and a.out is None and not a.plan_only and a.approved_plan is None,'read-only result-check route');print(json.dumps(check_result(a.check)));return
    need(a.manifest is not None and a.out is not None and a.expected_pi,'manifest/output/independent expected queries required');need(1<=a.jobs<=32 and 1<=a.memory_gib<=300 and 1<=a.gap_memory_gib<=300 and 1<=a.final_memory_gib<=300 and max(a.jobs*a.memory_gib,a.gap_memory_gib,a.final_memory_gib)<=a.aggregate_gib<=768,'individual<=300GiB; weighted aggregate<=768GiB');cpus=[int(x)for x in a.cpus.split(',')];need(len(cpus)==len(set(cpus))and len(cpus)>=a.jobs and set(cpus)<=os.sched_getaffinity(0),'distinct available worker CPUs');cpus=cpus[:a.jobs];expected=[]
    for item in a.expected_pi:need(re.fullmatch(r'[0-9]+=[0-9]+',item)is not None,'strict expected N=value');expected.append(tuple(map(int,item.split('='))))
    study=Study(a.manifest,a.context,expected,a.control);need(a.owned_scratch_root is None or a.owned_scratch_root.resolve()==study.scratch,'owned scratch root is the actual entire experiment');need(0<=a.scratch_estimate_gib<=300,'bounded explicit scratch estimate');need(a.expected_import_count is None or a.expected_import_count>=0,'nonnegative enumerated import count');need(a.control or a.expected_import_count is not None,'real research plans require explicit independently expected import count');records=imported_records(study,a.import_audit);imported=len(records)
    if a.expected_import_count is not None:need(imported==a.expected_import_count,'every independently expected successful import read back')
    disk=DiskMeter(study.scratch,a.scratch_estimate_gib*G);initial_disk=disk.measure(True);need(disk.okay(initial_disk)and initial_disk['allocated_bytes']+a.scratch_estimate_gib*G<=300*G,'independent1TiB free disk and300GiB owned scratch with estimated safe headroom');mem=available();need(mem>=1024*G and mem>=512*G+max(a.memory_gib,a.gap_memory_gib,a.final_memory_gib)*G,'actual1TiB available RAM and512GiB reserve before planning/launch');cfg=configuration(a,study,cpus);out=a.out.resolve();need(out.is_relative_to(study.scratch)and out!=study.scratch and not out.exists(),'fresh owned execution output');need(not(a.plan_only and a.approved_plan is not None),'separate planning and approved execution');out.mkdir(parents=True);reuse=dict(status='ALL_ENUMERATED_IMPORTED_SUCCESSES_INDEPENDENTLY_READ_BACK_NOT_FINAL_PROOF',count=imported,records=list(records.values()),manifest_sha256=sha(study.manifest),controller_sha256=sha(__file__));publish(out/'IMPORTED_READBACK.json',reuse);plan=dict(status='PLAN_ONLY_REQUIRES_ROOT_REVIEW_BEFORE_RESEARCH_LAUNCH',configuration=cfg,imported_readback=dict(path=str(out/'IMPORTED_READBACK.json'),sha256=sha(out/'IMPORTED_READBACK.json'),count=imported),resource_preflight=dict(memavailable_bytes=mem,disk=initial_disk,estimated_new_scratch_bytes=a.scratch_estimate_gib*G,estimate_is_not_a_measured_peak=True),resource_gate='Root reviews successful exact late Check2500 and measured VmPeak<=80GiB for8x96; otherwise reviewed6x128; no controller-generated approval',phases=['data_pool','drained_sequential_gapcheck','arithmetic_pool','drained_sequential_final','drained_sequential_complete_type_axiom_audit'],no_research_jobs_launched_by_plan=True);publish(out/'PLAN.json',plan)
    if a.plan_only:print(json.dumps(dict(status=plan['status'],plan=str(out/'PLAN.json'),sha256=sha(out/'PLAN.json'),imports_independently_validated=imported)));return
    need(a.control or a.approved_plan is not None,'research execution requires separately reviewed concrete plan');approved=None
    if a.approved_plan is not None:
        approved=read(a.approved_plan);need(approved['status']=='PLAN_ONLY_REQUIRES_ROOT_REVIEW_BEFORE_RESEARCH_LAUNCH'and approved['configuration']==json.loads(json.dumps(cfg)),'approved concrete plan exactly matches scientific/resource/controller configuration')
    (out/'logs').mkdir();journal=out/'RESERVATIONS.jsonl';journal.touch();failures=[];drain=[];started=time.monotonic();active={};peak_reserved=0;resource_pause=None
    def event(kind,name=None,cap=0,extra=None):
        nonlocal peak_reserved
        reserved=sum(x['cap']for x in active.values());peak_reserved=max(peak_reserved,reserved);e=dict(time_unix=time.time(),event=kind,module=name,cap_bytes=cap,reserved_bytes=reserved,host_memavailable_bytes=available(),disk=disk.last)
        if extra:e.update(extra)
        with journal.open('a')as f:f.write(json.dumps(e,allow_nan=False)+'\n');f.flush()
        return e
    def stopping(sig,frame):
        drain.append(signal.Signals(sig).name);event('drain_requested',extra=dict(reasons=drain))
    for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGUSR1]:signal.signal(sig,stopping)
    def state(phase):
        target=out/'RUN_STATE.json';tmp=target.with_suffix('.pending');tmp.write_text(json.dumps(dict(status='ACTIVE_OR_DRAINED_STATE_NOT_ACCEPTANCE',phase=phase,completed=len(set(records)&set(study.names)),total=len(study.names),active=[dict(module=n,pid=x['process'].pid,cpu=x['cpu'],cap_bytes=x['cap'])for n,x in active.items()],reserved_bytes=sum(x['cap']for x in active.values()),host_memavailable_bytes=available(),disk=disk.last,drain_reasons=drain,failures=failures),indent=2)+'\n');tmp.replace(target)
    def launch(name,cap,cpu,source_root=None):
        root=source_root or study.root;cmd=PYTHON+[str(S/'scripts/compile_lean.py'),name,'--source-root',str(root),'--audit-root',str(out/'audit'),'--memory-gib',str(cap//G),'--cpus',str(cpu)];log=out/'logs'/name;obs=out/'logs'/(name+'.process.json');active[name]=dict(process=None,cpu=cpu,cap=cap,stdout=None,stderr=None,initial=None,observed={},observation=obs,command=cmd);reserved=event('reserve',name,cap,dict(cpu=cpu))
        if reserved['host_memavailable_bytes']<max(1024*G,512*G+reserved['reserved_bytes'])or not disk.okay(reserved['disk']):del active[name];event('release',name,cap,dict(reason='resources_changed_before_dispatch'));return False
        try:
            x=active[name];x['stdout']=Path(str(log)+'.stdout').open('w');x['stderr']=Path(str(log)+'.stderr').open('w');proc=subprocess.Popen(cmd,stdout=x['stdout'],stderr=x['stderr']);x['process']=proc;x['initial']=snapshot(proc.pid);need(x['initial']is not None,'actual launched PID/start token');event('started',name,cap,dict(pid=proc.pid,start_token=x['initial']['start_token'],cpu=cpu));return True
        except Exception as error:
            x=active[name];failures.append(dict(module=name,classification='SPAWN_OR_PROCESS_OBSERVATION_FAILURE',error=repr(error)))
            if x['process']is None:
                for handle in [x['stdout'],x['stderr']]:
                    if handle is not None:handle.close()
                del active[name];event('release',name,cap,dict(reason='spawn_failed'))
            return False
    def poll(phase):
        for name,x in list(active.items()):
            for item in descendants(x['process'].pid):
                key=str(item['pid'])+':'+item['start_token'];prior=x['observed'].get(key)
                if prior:
                    item['vmpeak_bytes']=max(item['vmpeak_bytes']or 0,prior['vmpeak_bytes']or 0);item['rss_bytes']=max(item['rss_bytes']or 0,prior['rss_bytes']or 0)
                x['observed'][key]=item
            rc=x['process'].poll()
            if rc is None:continue
            x['stdout'].close();x['stderr'].close();observation=dict(module=name,initial=x['initial'],command=x['command'],memory_limit_bytes=x['cap'],actual_processes=list(x['observed'].values()),returncode=rc);x['observation'].write_text(json.dumps(observation,indent=2)+'\n');stdout=Path(str(out/'logs'/name)+'.stdout').read_text();del active[name];event('release',name,x['cap'],dict(returncode=rc,observation_sha256=sha(x['observation']),reason='start_observation_failed'if x['initial']is None else None))
            if rc!=0:
                failed=dict(module=name,returncode=rc,observation=str(x['observation']),classification='COMPILER_OR_NUMERICAL_REJECTION',linux_OOM_kill_evidence='not established')
                try:
                    emitted=strict_text(stdout.strip().splitlines()[-1]);receipt=Path(emitted['audit'])/'RUN.json';need(receipt.resolve().is_relative_to(out/'audit'),'owned failure receipt');fr=read(receipt);folder=receipt.parent;message=(folder/'stdout').read_text()+(folder/'stderr').read_text();failed.update(compiler_receipt=str(receipt),compiler_receipt_sha256=sha(receipt),actual_compiler_returncode=fr['returncode'],source_sha256=fr['source_sha256'],memory_limit_bytes=fr['memory_limit_bytes'])
                    if any(term in message.lower()for term in ['out of memory','memory allocation','failed to allocate']):failed['classification']='ADDRESS_SPACE_ALLOCATION_PANIC_NOT_PROVEN_OS_OOM'
                    elif fr['returncode']in[-9,137]or 'terminated by signal 9'in message.lower():failed['classification']='SIGKILL_CAUSE_UNESTABLISHED'
                except Exception as error:failed['failure_receipt_readback_error']=repr(error)
                failures.append(failed);continue
            try:
                emitted=strict_text(stdout.strip().splitlines()[-1]);receipt=Path(emitted['audit'])/'RUN.json'
                if name in study.by:proof=study.audit(name,receipt);records[name]=dict(module=name,compiler_receipt=str(receipt),proof=proof,reused=False,observation=str(x['observation']),observation_sha256=sha(x['observation']))
                else:records[name]=dict(module=name,compiler_receipt=str(receipt),observation=str(x['observation']),observation_sha256=sha(x['observation']))
            except Exception as error:failures.append(dict(module=name,error=repr(error),observation=str(x['observation'])))
        dispatch_allowed(0);state(phase)
    def dispatch_allowed(cap):
        nonlocal resource_pause
        reserved=sum(x['cap']for x in active.values());mem=available();space=disk.measure(force=cap>0);okay=disk.okay(space)and mem>=1024*G and mem>=512*G+reserved+cap and reserved+cap<=a.aggregate_gib*G
        reason=None if okay else dict(memavailable_bytes=mem,reserved_bytes=reserved,next_cap_bytes=cap,disk=space)
        if bool(reason)!=bool(resource_pause):event('resources_resumed'if okay else'resources_pause_new_dispatch',extra=reason)
        resource_pause=reason;return okay
    def run_phase(label,names,cap,sequential=False,source_root=None):
        pending=set(names)-set(records)
        while pending or active:
            poll(label)
            if not drain and not failures:
                idle=[c for c in cpus if c not in[x['cpu']for x in active.values()]]
                for name in sorted(pending):
                    if drain or failures:break
                    if not idle or(sequential and active):break
                    deps=set(study.by[name]['dependencies'])&set(study.names)if name in study.by else set(study.names)
                    if deps<=set(records)and dispatch_allowed(cap):
                        if launch(name,cap,idle.pop(0),source_root):pending.remove(name)
            if (drain or failures)and not active:return False
            if pending and not active and not any((set(study.by[n]['dependencies'])&set(study.names))<=set(records)for n in pending if n in study.by)and source_root is None:raise ValueError('cyclic/incomplete generated dependencies')
            if pending or active:time.sleep(.5)
        return True
    ns=study.d['namespace'];data=[n for n in study.names if study.by[n]['kind']=='data'];complete=False
    okay=run_phase('data_pool',data,a.memory_gib*G)
    if okay and a.stage!='data':okay=run_phase('drained_gapcheck',[ns+'.GapCheck'],a.gap_memory_gib*G,True)
    if okay and a.stage!='data':okay=run_phase('arithmetic_pool',study.checks,a.memory_gib*G)
    if okay and a.stage=='all':okay=run_phase('drained_final',[study.d['final_module']],a.final_memory_gib*G,True)
    exact_audit=None
    if okay and a.stage=='all'and set(records)==set(study.names):
        name='RamanujanPV.HighControllerAudit_'+sha(study.manifest)[:16];root=out/'controller-source';source=root/Path(*name.split('.')).with_suffix('.lean');source.parent.mkdir(parents=True);source.write_text(study.audit_text());okay=run_phase('drained_complete_exact_type_axiom_audit',[name],a.final_memory_gib*G,True,root)
        if okay:
            ar=records.pop(name);receipt=Path(ar['compiler_receipt']);exact_audit=dict(module=name,source_root=str(root),source=str(source),source_sha256=sha(source),receipt=str(receipt),receipt_sha256=sha(receipt),observation=ar['observation'],observation_sha256=ar['observation_sha256']);complete=True
    audit_peak=0
    if exact_audit is not None:
        usage=(Path(exact_audit['receipt']).parent/'rusage.txt').read_text();match=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',usage);need(match is not None,'actual complete-auditor RSS');audit_peak=int(match[1])*1024;exact_audit['peak_rss_bytes']=audit_peak
    need(not active,'all jobs drained before outcome');maximum=validate_journal(journal,a.aggregate_gib*G);need(maximum==peak_reserved,'independent scheduler accounting');result=dict(status='COMPLETE_HIGH_RESOURCE_KERNEL_CERTIFICATE_NOT_SOURCE_PV'if complete else('DRAINED_CHECKPOINT_NOT_ACCEPTANCE'if drain else('FAILED_ATTEMPTS_PRESERVED_NOT_ACCEPTANCE'if failures else'PARTIAL_STAGE_NOT_ACCEPTANCE')),configuration=cfg,plan=str(out/'PLAN.json'),plan_sha256=sha(out/'PLAN.json'),approved_plan=dict(path=str(a.approved_plan.resolve()),sha256=sha(a.approved_plan))if a.approved_plan else None,completed=len(records),records=list(records.values()),imported_successes=imported,seconds=time.monotonic()-started,actual_peak_worker_rss_bytes=max([x['proof']['peak_rss_bytes']for x in records.values()]+[audit_peak]),actual_aggregate_peak_RAM_measured=False,observed_owned_scratch_peak_bytes=disk.peak,final_disk_measurement=disk.measure(True),peak_reserved_bytes=peak_reserved,journal=str(journal),journal_sha256=sha(journal),final_audit=exact_audit,prime_count_results=study.d['results'],source_first_PV=False,failures=failures,drain_reasons=drain,remaining_boundary='This is a complete kernel certificate only when accepted; actual C source/output/driver/theorem composition remains separate.')
    if complete:
        candidate=out/'RESULT_CANDIDATE.json';publish(candidate,result);check_result(candidate);candidate.replace(out/'RESULT.json')
    else:publish(out/'CHECKPOINT.json',result)
    state('finished_complete'if complete else'finished_checkpoint');print(json.dumps(dict(status=result['status'],completed=len(records),total=len(study.names),seconds=result['seconds'])));need(not failures,'failed compiler/proof attempts retained; no complete acceptance')
if __name__=='__main__':main()
