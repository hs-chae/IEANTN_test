#!/usr/bin/env python3
"""Separate, resumable pure-kernel recovery of the locked 1.49e12 count.

Never writes the original proposal, object bank, receipts, or worker state.
Numerical checking is not source-first PV. The final consumer additionally
constructs the existing source/model execution, with its stated trust boundary.
"""
from pathlib import Path
import argparse, fcntl, hashlib, importlib.util, json, math, os, re, resource
import shutil, signal, subprocess, sys, threading, time

HERE=Path(__file__).resolve().parent
OLD=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network')
OS=OLD/'Solutions/RamanujanSourcePV.v1'
OD=Path('/data/ivy-ramanujan-source-pv-20261119')
PROPOSAL=OD/'high-transition-count-proposal-v1/proposal/PROPOSAL.json'
G=1<<30
STD={'propext','Classical.choice','Quot.sound'}
NS='RamanujanPV.HighTransitionCount'
CONTROLLER_OLD_SHA='ff9f23a4832c105e368f7cfe3c5ae400dbd5e4cec32c04a4c2135ea972d5ef63'

def need(ok,message):
    if not ok:raise ValueError(message)

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for block in iter(lambda:f.read(8<<20),b''):h.update(block)
    return h.hexdigest()

def read(path):
    def pairs(items):
        d={}
        for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,
        parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))

def save(path,value):
    path=Path(path);tmp=path.with_suffix(path.suffix+'.pending')
    tmp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');os.replace(tmp,path)

def available():
    return next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()
        if x.startswith('MemAvailable:'))

def disk(root):
    return sum(p.stat().st_blocks*512 for p in Path(root).rglob('*')
        if p.is_file()and not p.is_symlink())

def imports(text):
    # Captured application sources have ordinary single-line import headers.
    # The compiler independently checks their actual object dependencies later.
    return [m for line in text.splitlines()if line.startswith('import ')
        for m in line.split()[1:]if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',m)]

def rel(module,suffix='.lean'):return Path(*module.split('.')).with_suffix(suffix)

def old_study():
    controller=OS/'scripts/execute_demand_high_resource.py'
    need(sha(controller)==CONTROLLER_OLD_SHA,'original acceptance controller drift')
    sys.path.insert(0,str(OS/'scripts'))
    spec=importlib.util.spec_from_file_location('original_count_acceptance',controller)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    return m.Study(PROPOSAL,OS/'BUILD_CONTEXT.json',[(1490000000000,55206486339)])

def basis_readback(checkpoint,study):
    need(checkpoint['accepted_modules']==994 and len(checkpoint['records'])==994,
        'exact approved 994-module checkpoint')
    got={}
    for item in checkpoint['records']:
        name=item['module'];need(name not in got,'duplicate checkpoint module')
        actual=study.audit(name,item['compiler_receipt'])
        need(actual==item['proof'],'independent original receipt/source/object/log readback')
        got[name]=actual
    need(len([n for n in got if '.Check'in n])==299 and NS+'.GapCheck'in got,
        'approved arithmetic/gap census')
    need((set(study.names)-set(got))==set(checkpoint['remaining_arithmetic_checks'])|{NS+'.Final'},
        'all and only2469 arithmetic plus Final missing')
    return got

def leaf_text(index,start,size):
    lines=['import '+NS+'.Data','import PureBalancedCheck',
        'namespace '+NS,'open QuotientDemandCheck RHOcticPush.PureBalancedCount',
        'set_option maxHeartbeats 0','set_option maxRecDepth 1000000',
        'set_option Elab.async false']
    if size==32768:
        lines+=['private theorem numeric_'+index+' : tree (checkEntry nodes gaps gapCount) 15 '+str(start)+'=true := by decide +kernel',
            'theorem part_'+index+' : allFrom (checkEntry nodes gaps gapCount) '+str(start)+' 32768=true :=',
            '  source_32768 numeric_'+index]
    else:
        depths=[d for d in reversed(range(size.bit_length()))if size&(1<<d)]
        offset=0;parts=[]
        for k,d in enumerate(depths):
            name='tail_'+index+'_'+str(k);parts.append((name,offset,1<<d))
            lines+=['private theorem '+name+'_numeric : tree (checkEntry nodes gaps gapCount) '+str(d)+' '+str(start+offset)+'=true := by decide +kernel',
                'private theorem '+name+' : allFrom (checkEntry nodes gaps gapCount) '+str(start+offset)+' '+str(1<<d)+'=true := tree_sound '+name+'_numeric']
            offset+=1<<d
        need(offset==size,'complete tail binary partition')
        name,offset,n=parts[-1];acc=name;total=n
        for k,(name,offset,n)in reversed(list(enumerate(parts[:-1]))):
            new='tail_union_'+index+'_'+str(k)
            lines+=['private theorem '+new+' : allFrom (checkEntry nodes gaps gapCount) '+str(start+offset)+' '+str(n+total)+'=true :=',
                '  (RHOcticPush.BalancedCount.append_pure (checkEntry nodes gaps gapCount) '+str(n)+' '+str(total)+' '+str(start+offset)+').trans (congrArg₂ Bool.and '+name+' '+acc+')']
            acc=new;total+=n
        lines+=['theorem part_'+index+' : allFrom (checkEntry nodes gaps gapCount) '+str(start)+' '+str(size)+'=true := '+acc]
    lines+=['#print axioms part_'+index,'end '+NS]
    return '\n'.join(lines)+'\n'

def closed_consumer():
    return '''import RamanujanPV.HighTransitionCount.Final
import RamanujanPV.QuotientCountRealization
namespace RHOcticPush.RecoveredCount
theorem count : Nat.primeCounting 1490000000000=55206486339 :=
  RamanujanPV.HighTransitionCount.pi_1490000000000
theorem actual_C_model_execution :
    RamanujanPV.QuotientCCell.SourceExecution 1490000000000 55206486339 :=
  RamanujanPV.QuotientCountRealization.source_execution_from_kernel_value
    (by norm_num) (by norm_num) count
theorem exact_source_bytes_and_execution :
    RamanujanPV.QuotientCSourceV2.render ()=some RamanujanPV.QuotientCSourceV2.actualSource ∧
    RamanujanPV.QuotientDriverSource.render RamanujanPV.QuotientDriverSource.program=
      some RamanujanPV.QuotientDriverSource.actualSource ∧
    RamanujanPV.QuotientCCell.SourceExecution 1490000000000 55206486339 :=
  ⟨RamanujanPV.QuotientCSourceV2.actual_source_bytes,
    RamanujanPV.QuotientDriverSource.actual_source_bytes,actual_C_model_execution⟩
#print axioms count
#print axioms actual_C_model_execution
#print axioms exact_source_bytes_and_execution
end RHOcticPush.RecoveredCount
'''

def prepare(out):
    controller_before=sha(__file__)
    out=out.resolve();need(not out.exists(),'fresh experiment-owned output required')
    need(str(out).startswith('/data/ivy-rh-octic-20261123/ramanujan/'),'owned scratch prefix')
    study=old_study();cp=read(HERE/'ORIGINAL_ACCEPTED_CHECKPOINT.json');basis=basis_readback(cp,study)
    need(sha(__file__)==controller_before,'preparation controller changed during baseline readback')
    out.mkdir(parents=True);src=out/'source';src.mkdir()
    for d in ['objects','union','attempts','dependencies']:(out/d).mkdir()
    (out/'ORIGINAL_CHECKPOINT.json').write_bytes((HERE/'ORIGINAL_ACCEPTED_CHECKPOINT.json').read_bytes())
    (out/'recover_count.executed.py').write_bytes(Path(__file__).read_bytes())
    modules=[];resources=[];done=set(basis)
    def add(name,text,kind,original=None):
        p=src/rel(name);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
        row=dict(module=name,source_sha256=sha(p),kind=kind,imports=imports(text),original=original)
        modules.append(row);done.add(name)
    active=set()
    def core(name):
        if name in done:return
        p=OS/rel(name)
        if not p.is_file():p=OLD/rel(name)
        if not p.is_file():return # Generic imports are checked against pinned libraries.
        need(name not in active,'application import cycle');active.add(name)
        text=p.read_text()
        for m in imports(text):core(m)
        active.remove(name);add(name,text,'core',dict(path=str(p),sha256=sha(p)))
        for inc in re.findall(r'include_str\s+"([^"]+)"',text):
            original=(p.parent/inc).resolve();target=(src/rel(name).parent/inc).resolve()
            need(target.is_relative_to(src),'owned included-resource destination')
            target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(original.read_bytes())
            row=dict(source=str(original),relative=str(target.relative_to(src)),sha256=sha(original))
            if row not in resources:resources.append(row)
    core('RamanujanPV.QuotientDemandCheck');core('RamanujanPV.QuotientCountRealization')
    add('BalancedCountCheck',(HERE.parent/'BalancedCountCheck.lean').read_text(),'bridge',
        dict(path=str(HERE.parent/'BalancedCountCheck.lean'),sha256=sha(HERE.parent/'BalancedCountCheck.lean')))
    add('PureBalancedCheck',(HERE/'PureBalancedCheck.lean').read_text(),'bridge',
        dict(path=str(HERE/'PureBalancedCheck.lean'),sha256=sha(HERE/'PureBalancedCheck.lean')))
    remaining=cp['remaining_arithmetic_checks']
    for name in remaining:
        index=name[-4:];i=int(index);size=min(32768,90670946-i*32768)
        text=leaf_text(index,i*32768,size);original=study.by[name]
        add(name,text,'arithmetic',dict(path=original['source'],sha256=original['sha256']))
        modules[-1]['range']=[i*32768,size]
        need(re.search(r'theorem part_'+index+r' : ([^\n]+?) :=',text)[1]==
            re.search(r'theorem part_'+index+r' : ([^\n]+?) :=',Path(original['source']).read_text())[1],
            'exact unchanged original part statement')
    final=study.by[NS+'.Final'];add(NS+'.Final',Path(final['source']).read_text(),'final',
        dict(path=final['source'],sha256=final['sha256']))
    add('RecoveredCountConsumer',closed_consumer(),'consumer')
    add('RecoveredCountAudit',study.audit_text()+'\nimport RecoveredCountConsumer\n','audit')
    # Lean imports must precede declarations; put the consumer import in the header.
    ap=src/'RecoveredCountAudit.lean';ap.write_text('import RecoveredCountConsumer\n'+study.audit_text())
    modules[-1]['source_sha256']=sha(ap)
    modules[-1]['imports']=imports(ap.read_text())
    audit_symbols=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)',study.audit_text(),re.M)
    need([s for s in audit_symbols if s.startswith(NS+'.part_')]==
        [NS+'.part_'+format(i,'04d')for i in range(2768)],'all2768 exact numerical audit symbols')
    need(all(NS+'.'+n in audit_symbols for n in
        ['gaps_checked','entries_checked','root_1490000000000','pi_1490000000000']),
        'gap, full-range entries, twelve-field root, exact count audit symbols')
    ctx=read(OS/'BUILD_CONTEXT.json')
    for name,row in basis.items():
        link=out/'union'/rel(name,'.olean');link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(row['object'])
    m=dict(schema='RH_PURE_COUNT_POSTHOC_RECOVERY_V1',mathematical_target=[1490000000000,55206486339],
        records=90670946,original_proposal=str(PROPOSAL),original_proposal_sha256=sha(PROPOSAL),
        packed_file=study.d['packed_file'],packed_sha256=study.d['packed_sha256'],
        old_controller_sha256=CONTROLLER_OLD_SHA,checkpoint_sha256=sha(out/'ORIGINAL_CHECKPOINT.json'),
        basis=basis,context=ctx,context_sha256=sha(OS/'BUILD_CONTEXT.json'),
        controller_sha256=controller_before,generator_sha256=controller_before,modules=modules,resources=resources,
        exact_original_audit_symbols=audit_symbols,
        remaining_arithmetic=len(remaining),total_original_modules=3464,
        pure_checker_not_source_first_PV=True,old_workers_untouched=True,
        resource_policy=dict(host_reserve_bytes=512*G,initial_MinAvailable_bytes=1024*G,
            per_compiler_AS_bytes=128*G,final_AS_bytes=256*G,max_jobs=16,
            initial_physical_per_job_bytes=38*G,physical_margin_factor=1.20,
            max_scratch_bytes=300*G,min_initial_disk_free_bytes=1024*G))
    need(len(remaining)==2469 and len(basis)==994,'complete locked recovery census')
    need(sha(__file__)==controller_before,'preparation controller changed during generation')
    save(out/'MANIFEST.json',m)
    save(out/'PLAN.json',dict(status='PREPARED_NO_NEW_COMPILER_LAUNCHED',manifest_sha256=sha(out/'MANIFEST.json'),
        MemAvailable_bytes=available(),disk_free_bytes=shutil.disk_usage(out).free,
        generated_modules=len(modules),remaining_arithmetic=2469,basis_modules=994,
        final_gates=['all2469 exact empty-axiom parts','unchanged Final','complete exact-type/axiom audit',
            'closed actual C source-byte/model-execution consumer','source/object/log/dependency readback']))
    return m

def manifest(out,full_basis=True):
    m=read(out/'MANIFEST.json');need(m['schema']=='RH_PURE_COUNT_POSTHOC_RECOVERY_V1','schema')
    need(sha(__file__)==m['controller_sha256']==sha(out/'recover_count.executed.py'),'frozen controller identity')
    need(m['mathematical_target']==[1490000000000,55206486339]and m['remaining_arithmetic']==2469,
        'fixed mathematical target/census')
    need(sha(OS/'BUILD_CONTEXT.json')==m['context_sha256']and sha(m['context']['compiler'])==m['context']['compiler_sha256'],
        'pinned generic context/compiler')
    for d in m['context']['generic_dependencies']:
        p=subprocess.run(['git','rev-parse','HEAD'],cwd=d['path'],capture_output=True,text=True)
        need(p.returncode==0 and p.stdout.strip()==d['revision'],'generic dependency revision')
        need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=d['path']).returncode==0,'generic tracked source drift')
    need(sha(PROPOSAL)==m['original_proposal_sha256']and sha(out/'ORIGINAL_CHECKPOINT.json')==m['checkpoint_sha256'],
        'original immutable proposal/checkpoint')
    if full_basis:
        study=old_study();need(basis_readback(read(out/'ORIGINAL_CHECKPOINT.json'),study)==m['basis'],
            'complete original basis independent readback')
    names=[q['module']for q in m['modules']];need(len(names)==len(set(names)),'unique generated compiler identities')
    expected=set(read(out/'ORIGINAL_CHECKPOINT.json')['remaining_arithmetic_checks'])
    need({q['module']for q in m['modules']if q['kind']=='arithmetic'}==expected,'every remaining exact chunk')
    for q in m['modules']:
        p=out/'source'/rel(q['module']);need(p.is_file()and not p.is_symlink()and sha(p)==q['source_sha256'],'frozen generated source')
        if q['original']:need(sha(q['original']['path'])==q['original']['sha256'],'preserved original source')
    for q in m['resources']:
        need(sha(q['source'])==q['sha256']==sha(out/'source'/q['relative']),'actual included source resource')
    return m

def reports(text,symbols,empty=False):
    found={}
    for symbol in symbols:
        a=re.findall(r"'"+re.escape(symbol)+r"' does not depend on any axioms",text)
        b=re.findall(r"'"+re.escape(symbol)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
        need(len(a)+len(b)==1,'one actual named axiom report:'+symbol)
        axioms=[]if a else[x.strip()for x in b[0].split(',')if x.strip()]
        need(set(axioms)<=STD and(not empty or not axioms),'exact theorem axiom policy:'+symbol)
        found[symbol]=axioms
    return found

def required(q):
    if q['kind']=='arithmetic':return [NS+'.part_'+q['module'][-4:]]
    if q['kind']=='final':return [NS+'.pi_1490000000000']
    if q['kind']=='consumer':return ['RHOcticPush.RecoveredCount.'+n for n in ['count','actual_C_model_execution','exact_source_bytes_and_execution']]
    if q['kind']=='bridge'and q['module']=='PureBalancedCheck':
        return ['RHOcticPush.PureBalancedCount.'+n for n in ['tree','tree_eq','tree_sound','source_32768']]
    return []

def command(out,m,q,attempt,cpu):
    cap=256*G if q['kind']in ['final','audit','consumer']else 128*G
    return ['taskset','-c',str(cpu),'/usr/bin/prlimit','--as='+str(cap),'--',
        '/usr/bin/time','-v','-o',str(attempt/'resources.txt'),m['context']['compiler'],
        '--root='+str(out/'source'),'-j1',str(out/'source'/rel(q['module'])),
        '-o',str(out/'objects'/rel(q['module'],'.olean'))]

def audit_receipt(out,m,q,path):
    r=read(path);a=path.parent
    need(r['status']=='PASS'and type(r['returncode'])is int and r['returncode']==0,'successful actual compiler receipt')
    need(r['module']==q['module']and r['source_sha256']==q['source_sha256'],'exact source/module receipt')
    need(r['command']==command(out,m,q,a,r['cpu']),'exact compiler/source/object/AS command')
    for f in ['stdout','stderr','resources.txt']:
        need(sha(a/f)==r[f+'_sha256'],'actual compiler log hash')
    obj=out/'objects'/rel(q['module'],'.olean');need(sha(obj)==r['object_sha256'],'actual object hash')
    text=(a/'stdout').read_text();err=(a/'stderr').read_text()
    need(not any(v in text+err for v in ['sorryAx','Lean.ofReduceBool','declaration uses `sorry`']),'forbidden native/admit fact')
    need(reports(text,required(q),q['kind']=='arithmetic')==r['axioms'],'actual exact axiom reports')
    if q['kind']=='bridge'and q['module']=='PureBalancedCheck':reports(text,required(q),True)
    if q['kind']=='audit':
        study=old_study()
        for s in re.findall(r'^#print axioms ([A-Za-z0-9_.]+)',study.audit_text(),re.M):
            reports(text,[s],s.rsplit('.',1)[-1].startswith(('part_','gaps_checked','root_')))
    usage=(a/'resources.txt').read_text();rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',usage)
    need(rss is not None and r['peak_RSS_bytes']==int(rss[1])*1024,'actual child RSS metric')
    return r

def process(pid,pss=False):
    try:
        p=Path('/proc')/str(pid);s=(p/'stat').read_text().rsplit(')',1)[1].split()
        d={l.split(':',1)[0]:l.split(':',1)[1].strip()for l in(p/'status').read_text().splitlines()if':'in l}
        if pss:d.update({l.split(':',1)[0]:l.split(':',1)[1].strip()for l in(p/'smaps_rollup').read_text().splitlines()if':'in l})
        return dict(pid=pid,start_ticks=s[19],ppid=int(s[1]),**{k:int(d[k].split()[0])*1024
            for k in ['VmRSS','VmPeak','VmHWM','Pss','Private_Dirty','Private_Clean']if k in d})
    except (OSError,ValueError,IndexError):return None

def process_tree(root,pss=False):
    todo=[root];rows=[];seen=set()
    while todo:
        pid=todo.pop()
        if pid in seen:continue
        seen.add(pid);row=process(pid,pss)
        if row:rows.append(row)
        try:todo.extend(map(int,Path('/proc',str(pid),'task',str(pid),'children').read_text().split()))
        except OSError:pass
    return rows

def deps_check(out,m,q):
    env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'union'),*m['context']['generic_libraries']])
    cmd=[m['context']['compiler'],'--root='+str(out/'source'),'--deps',str(out/'source'/rel(q['module']))]
    cp=subprocess.run(cmd,cwd=out/'source',env=env,capture_output=True,text=True)
    need(cp.returncode==0,'actual dependency probe')
    base=out/'dependencies'/q['module'];so=Path(str(base)+'.stdout');se=Path(str(base)+'.stderr')
    so.write_text(cp.stdout);se.write_text(cp.stderr)
    allowed={str((out/'objects'/rel(v['module'],'.olean')).resolve())for v in m['modules']}
    allowed|={str(Path(v['object']).resolve())for v in m['basis'].values()}
    generic=[Path(p).resolve()for p in m['context']['generic_libraries']]
    generic+=[Path(m['context']['compiler']).resolve().parents[1]/'lib/lean']
    for line in cp.stdout.splitlines():
        p=Path(line).resolve();need(str(p)in allowed or any(p.is_relative_to(g)for g in generic),'foreign application dependency:'+str(p))
    return dict(module=q['module'],command=cmd,returncode=cp.returncode,
        stdout_sha256=sha(so),stderr_sha256=sha(se))

def historical_evidence(out):
    """Derive whole-campaign failures and measurements, including prior attempts."""
    failures=[];explicit=[];sigkills=[];receipts=[];childmax=0;incomplete=[]
    for p in sorted((out/'attempts').rglob('RECEIPT.json')):
        r=read(p);receipts.append(dict(path=str(p),sha256=sha(p)))
        if type(r.get('peak_RSS_bytes'))is int:childmax=max(childmax,r['peak_RSS_bytes'])
        text='\n'.join((p.parent/n).read_text(errors='replace')for n in ['stdout','stderr']if(p.parent/n).is_file())
        item=dict(receipt=str(p),receipt_sha256=sha(p),module=r['module'],returncode=r['returncode'])
        if r['status']!='PASS':failures.append(item)
        if re.search(r'out of memory|cannot allocate memory|bad_alloc',text,re.I):explicit.append(item)
        if r['returncode']in[-9,137]:sigkills.append(item)
    for parent in (out/'attempts').iterdir():
        if not parent.is_dir():continue
        for p in parent.iterdir():
            if p.is_dir()and not(p/'RECEIPT.json').exists():
                incomplete.append(dict(path=str(p),files=[dict(name=f.name,sha256=sha(f))
                    for f in sorted(p.iterdir())if f.is_file()]))
    peaks=dict(sampled_aggregate_RSS_bytes=0,sampled_aggregate_PSS_bytes=0,
        sampled_individual_VmPeak_bytes=0,sampled_owned_disk_bytes=0,
        actual_max_individual_child_RSS_bytes=childmax,samples=0)
    p=out/'RESOURCE_SAMPLES.jsonl'
    if p.exists():
        for line in p.open():
            r=json.loads(line);peaks['samples']+=1
            for k,f in [('sampled_aggregate_RSS_bytes','aggregate_RSS_bytes'),
                ('sampled_aggregate_PSS_bytes','aggregate_PSS_bytes'),('sampled_owned_disk_bytes','owned_disk_bytes')]:
                if type(r.get(f))is int:peaks[k]=max(peaks[k],r[f])
            peaks['sampled_individual_VmPeak_bytes']=max([peaks['sampled_individual_VmPeak_bytes']]+
                [q.get('VmPeak',0)for q in r['processes']])
    stops=[]
    p=out/'DISPATCH.jsonl'
    if p.exists():
        for line in p.open():
            r=json.loads(line)
            if r['event']=='resource_stop':stops.append(r)
    controller_failures=[dict(path=str(p),sha256=sha(p))for p in sorted(out.glob('FAILURE-*.json'))]
    controller_attempts=[]
    for p in sorted((out/'CONTROLLER_ATTEMPTS').glob('*/END.json')):
        controller_attempts.append(dict(path=str(p),sha256=sha(p),elapsed_seconds=read(p)['elapsed_seconds']))
    return dict(all_compiler_receipts=receipts,failed_attempts=failures,
        incomplete_compiler_attempts=incomplete,controller_failures=controller_failures,
        completed_controller_attempts=controller_attempts,
        total_active_controller_seconds=sum(r['elapsed_seconds']for r in controller_attempts),
        explicit_application_allocation_failure_reports=explicit,
        SIGKILL_deaths_with_unattributed_cause=sigkills,intentional_host_reserve_stops=stops,
        confirmed_kernel_OOM_kills=None,
        OOM_attribution='Kernel OOM attribution is unavailable; SIGKILL alone is not called an OOM. All failure history is retained.',
        whole_campaign_resource_peaks=peaks)

def validate(out,candidate=None):
    m=manifest(out);r=read(candidate or out/'RESULT.json')
    need(r['status']=='COMPLETE_EXACT_COUNT_AND_SOURCE_MODEL_EXECUTION','no partial acceptance')
    need(r['manifest_sha256']==sha(out/'MANIFEST.json')and r['controller_sha256']==sha(__file__),'receipt frozen source binding')
    need(len(r['records'])==len(m['modules'])and [x['module']for x in r['records']]==[q['module']for q in m['modules']],
        'complete exact ordered module population')
    for q,row in zip(m['modules'],r['records']):need(audit_receipt(out,m,q,Path(row['receipt']))==row['proof'],'independent actual proof readback')
    need(len(m['basis'])+sum(q['kind']in ['arithmetic','final']for q in m['modules'])==3464,'complete original universe')
    need(r['actual_count']==[1490000000000,55206486339]and r['new_source_first_PV_claim']is False,'exact result/trust scope')
    need(r['resource_samples_sha256']==sha(out/'RESOURCE_SAMPLES.jsonl'),'actual resource evidence')
    need(r['whole_campaign_evidence']==historical_evidence(out),'all-attempt failures/resource readback')
    need(r['owned_scratch_final_bytes']<=300*G and disk(out)<=300*G,'experiment-owned scratch bound')
    need([x['module']for x in r['dependency_probes']]==[NS+'.Final','RecoveredCountConsumer','RecoveredCountAudit'],
        'complete dependency probe inventory')
    for row in r['dependency_probes']:need(row==deps_check(out,m,next(q for q in m['modules']if q['module']==row['module'])),'dependency proof-closure readback')
    return r

def run(out,max_jobs,resume=False):
    out=out.resolve();need(not(out/'RESULT.json').exists(),'accepted run is immutable')
    lock=(out/'CONTROLLER.lock').open('a')
    fcntl.flock(lock.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
    m=manifest(out);need(1<=max_jobs<=16,'bounded CPU lanes')
    need(available()>=1024*G,'genuinely1TiB RAM available initially')
    need(shutil.disk_usage(out).free>=1024*G,'independent1TiB free disk initially')
    need(disk(out)<=300*G,'owned scratch cap')
    old=(out/'RUN_STATE.json').exists();need(not old or resume,'explicit resumption required')
    records={};done=set(m['basis']);by={q['module']:q for q in m['modules']}
    for q in m['modules']:
        accepted=out/'attempts'/q['module']/'ACCEPTED.json'
        if accepted.exists():
            row=read(accepted);r=audit_receipt(out,m,q,Path(row['receipt']))
            need(row['proof']==r,'resume exact proof receipt');records[q['module']]=row;done.add(q['module'])
    for name,row in records.items():
        need(set(by[name]['imports'])&set(by)<=done,'resume dependency closure')
        link=out/'union'/rel(name,'.olean');link.parent.mkdir(parents=True,exist_ok=True)
        obj=out/'objects'/rel(name,'.olean')
        if link.is_symlink():need(link.resolve()==obj,'resume exact union object')
        else:need(not link.exists(),'no foreign union object');link.symlink_to(obj)
    env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'union'),*m['context']['generic_libraries']]);env['PYTHONDONTWRITEBYTECODE']='1'
    cpus=[c for c in sorted(os.sched_getaffinity(0))if c not in range(112,120)]
    need(len(cpus)>=max_jobs,'distinct CPU affinity lanes')
    active={};failures=[];drain=[];peaks=dict(RSS=0,PSS=0,VmPeak=0,individual_RSS=0,disk=disk(out));start=time.monotonic();last_slow=0
    samples=(out/'RESOURCE_SAMPLES.jsonl').open('a');journal=(out/'DISPATCH.jsonl').open('a')
    attempt_parent=out/'CONTROLLER_ATTEMPTS';attempt_parent.mkdir(exist_ok=True);attempt_id=1
    while(attempt_parent/str(attempt_id)).exists():attempt_id+=1
    attempt_dir=attempt_parent/str(attempt_id);attempt_dir.mkdir()
    save(attempt_dir/'START.json',dict(unix=time.time(),pid=os.getpid(),resume=resume,
        initial_readback_modules=len(records),controller_sha256=sha(__file__)))
    def event(kind,**kw):journal.write(json.dumps(dict(unix=time.time(),event=kind,**kw))+'\n');journal.flush()
    def stopping(sig,frame):drain.append(signal.Signals(sig).name);event('drain_requested',signal=drain[-1])
    for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGUSR1]:signal.signal(sig,stopping)
    save(out/'LIVE_IDENTITY.json',dict(pid=os.getpid(),start_ticks=process(os.getpid())['start_ticks'],
        controller_sha256=sha(__file__),manifest_sha256=sha(out/'MANIFEST.json'),started_unix=time.time()))
    def state():save(out/'RUN_STATE.json',dict(status='RUNNING_OR_DRAINED_NOT_ACCEPTANCE',
        complete_new_modules=len(records),new_modules=len(m['modules']),accepted_original_modules=994,
        complete_arithmetic=299+sum(by[n]['kind']=='arithmetic'for n in records),
        total_arithmetic=2768,active=[dict(module=n,pid=x['p'].pid,start_ticks=x['start_ticks'],cpu=x['cpu'])for n,x in active.items()],
        elapsed_seconds_this_attempt=time.monotonic()-start,MemAvailable_bytes=available(),
        resource_peaks_this_attempt=peaks,failures_this_attempt=failures,drain_this_attempt=drain,
        all_prior_attempts_preserved_under=str(out/'CONTROLLER_ATTEMPTS')))
    def launch(q,cpu):
        mod=q['module'];parent=out/'attempts'/mod;parent.mkdir(parents=True,exist_ok=True)
        num=1
        while(parent/str(num)).exists():num+=1
        a=parent/str(num);a.mkdir();obj=out/'objects'/rel(mod,'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        cmd=command(out,m,q,a,cpu);fo=(a/'stdout').open('w');fe=(a/'stderr').open('w')
        p=subprocess.Popen(cmd,cwd=out/'source',env=env,stdout=fo,stderr=fe,start_new_session=True)
        first=process(p.pid);need(first is not None,'observed owned compiler start token')
        active[mod]=dict(p=p,a=a,cpu=cpu,cmd=cmd,start=time.monotonic(),start_ticks=first['start_ticks'],fo=fo,fe=fe)
        event('started',module=mod,pid=p.pid,start_ticks=first['start_ticks'],cpu=cpu,
            host_MemAvailable_bytes=available(),AS_bytes=256*G if q['kind']in['final','consumer','audit']else 128*G)
    try:
        while len(records)<len(m['modules']):
            slow=time.monotonic()-last_slow>=10
            rows=process_tree(os.getpid(),slow);rss=sum(x.get('VmRSS',0)for x in rows);pss=sum(x.get('Pss',0)for x in rows)
            mem=available();peaks['RSS']=max(peaks['RSS'],rss)
            if slow:
                last_slow=time.monotonic();peaks['PSS']=max(peaks['PSS'],pss);peaks['disk']=max(peaks['disk'],disk(out))
            peaks['VmPeak']=max([peaks['VmPeak']]+[x.get('VmPeak',0)for x in rows])
            peaks['individual_RSS']=max([peaks['individual_RSS']]+[x.get('VmRSS',0)for x in rows])
            samples.write(json.dumps(dict(unix=time.time(),MemAvailable_bytes=mem,aggregate_RSS_bytes=rss,
                aggregate_PSS_bytes=pss if slow else None,owned_disk_bytes=peaks['disk']if slow else None,
                processes=rows,active=len(active)))+'\n');samples.flush()
            need(peaks['disk']<=300*G,'experiment-owned scratch exhausted')
            if mem<512*G and active:
                # Only this controller's exact, newly-owned child groups may be stopped.
                n=max(active,key=lambda n:active[n]['start']);x=active[n]
                now=process(x['p'].pid);need(now is not None and now['start_ticks']==x['start_ticks'],'owned PID identity before resource stop')
                event('resource_stop',module=n,pid=x['p'].pid,host_MemAvailable_bytes=mem)
                os.killpg(x['p'].pid,signal.SIGTERM);drain.append('HOST_RESERVE_RESOURCE_STOP')
            finished=[]
            for mod,x in list(active.items()):
                code=x['p'].poll()
                if code is None:continue
                x['fo'].close();x['fe'].close();a=x['a'];q=by[mod];text=(a/'stdout').read_text();usage=(a/'resources.txt').read_text()
                match=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',usage)
                r=dict(status='PASS'if code==0 else'FAILED_ATTEMPT_PRESERVED',module=mod,returncode=code,
                    command=x['cmd'],cpu=x['cpu'],seconds=time.monotonic()-x['start'],source_sha256=sha(out/'source'/rel(mod)),
                    peak_RSS_bytes=int(match[1])*1024 if match else None,
                    axioms=reports(text,required(q),q['kind']=='arithmetic')if code==0 else{},
                    **{f+'_sha256':sha(a/f)for f in ['stdout','stderr','resources.txt']})
                if code==0:r['object_sha256']=sha(out/'objects'/rel(mod,'.olean'))
                save(a/'RECEIPT.json',r);finished.append(mod)
                if code!=0:failures.append(dict(module=mod,receipt=str(a/'RECEIPT.json'),returncode=code));drain.append('COMPILATION_FAILURE');continue
                audit_receipt(out,m,q,a/'RECEIPT.json');row=dict(module=mod,receipt=str(a/'RECEIPT.json'),proof=r)
                save(a.parent/'ACCEPTED.json',row);records[mod]=row;done.add(mod)
                link=out/'union'/rel(mod,'.olean');link.parent.mkdir(parents=True,exist_ok=True)
                need(not link.exists(),'fresh exact compiler namespace');link.symlink_to(out/'objects'/rel(mod,'.olean'))
                event('accepted',module=mod,seconds=r['seconds'],peak_RSS_bytes=r['peak_RSS_bytes'])
                print(len(records),len(m['modules']),mod,round(r['seconds'],2),flush=True)
            for mod in finished:del active[mod]
            if drain and not active:break
            if not drain:
                used={x['cpu']for x in active.values()}
                # Reserve physical headroom; address-space caps are not RAM reservations.
                observed=max([33*G]+[r['proof']['peak_RSS_bytes']for r in records.values()if by[r['module']]['kind']=='arithmetic'])
                budget=max(38*G,math.ceil(observed*1.20))
                free_slots=max_jobs-len(active)
                for q in m['modules']:
                    name=q['module']
                    if free_slots<=0:break
                    if name in done or name in active:continue
                    if not(set(q['imports'])&set(by)<=done):continue
                    heavy=q['kind']in['final','audit','consumer']
                    if heavy and active:continue
                    # Existing jobs have already reduced MemAvailable. Reserve their
                    # potential remaining physical growth plus the proposed new job.
                    growth=sum(max(0,budget-sum(r.get('VmRSS',0)for r in process_tree(x['p'].pid)))for x in active.values())
                    required_mem=256*G if heavy else budget
                    if available()<512*G+growth+required_mem:break
                    if shutil.disk_usage(out).free<1024*G:break
                    cpu=next(c for c in cpus if c not in used);launch(q,cpu);used.add(cpu);free_slots-=1
                    if heavy:break
            state();time.sleep(.5)
        if drain:save(out/'STOPPED.json',dict(status='DRAINED_INCOMPLETE_NOT_ACCEPTANCE',reasons=drain,failures=failures));return
        probes=[deps_check(out,m,by[n])for n in [NS+'.Final','RecoveredCountConsumer','RecoveredCountAudit']]
        samples.close();journal.close();state()
        save(attempt_dir/'END.json',dict(unix=time.time(),elapsed_seconds=time.monotonic()-start,
            complete_new_modules=len(records),resource_peaks_this_attempt=peaks,
            failures_this_attempt=failures,drain_this_attempt=drain,
            status='ALL_COMPILERS_COMPLETE_BEFORE_FINAL_INDEPENDENT_ACCEPTANCE'))
        result=dict(status='COMPLETE_EXACT_COUNT_AND_SOURCE_MODEL_EXECUTION',actual_count=[1490000000000,55206486339],
            manifest_sha256=sha(out/'MANIFEST.json'),controller_sha256=sha(__file__),
            records=[records[q['module']]for q in m['modules']],dependency_probes=probes,
            resource_samples_sha256=sha(out/'RESOURCE_SAMPLES.jsonl'),resource_peaks_this_attempt=peaks,
            whole_campaign_evidence=historical_evidence(out),
            owned_scratch_final_bytes=disk(out),seconds_this_attempt=time.monotonic()-start,
            new_source_first_PV_claim=False,
            trust='Ordinary kernel certificate plus actual rendered C source/model execution. Independent C parser soundness and physical native process/stdout association are not established. Pinned compiler/runtime/OS/hardware and model-interpretation contracts remain.',
            original_jobs_sources_results_unchanged=True)
        save(out/'CANDIDATE.json',result);validate(out,out/'CANDIDATE.json');os.replace(out/'CANDIDATE.json',out/'RESULT.json')
        print(result['status'],flush=True)
    except BaseException as error:
        save(out/('FAILURE-'+str(int(time.time()))+'.json'),dict(error=repr(error),
            complete_new_modules=len(records),active_owned=list(active),status='NO_ACCEPTANCE'))
        raise
    finally:
        for x in active.values():
            if x['p'].poll()is None:
                now=process(x['p'].pid)
                if now is not None and now['start_ticks']==x['start_ticks']:
                    os.killpg(x['p'].pid,signal.SIGTERM)
                    try:x['p'].wait(timeout=10)
                    except subprocess.TimeoutExpired:os.killpg(x['p'].pid,signal.SIGKILL);x['p'].wait()
            x['fo'].close();x['fe'].close()
        if not samples.closed:samples.close()
        if not journal.closed:journal.close()
        if not(attempt_dir/'END.json').exists():
            save(attempt_dir/'END.json',dict(unix=time.time(),elapsed_seconds=time.monotonic()-start,
                complete_new_modules=len(records),resource_peaks_this_attempt=peaks,
                failures_this_attempt=failures,drain_this_attempt=drain,
                final_acceptance=(out/'RESULT.json').exists()))
        lock.close()

def main():
    a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--prepare',type=Path);a.add_argument('--run',type=Path)
    a.add_argument('--verify',type=Path);a.add_argument('--check',type=Path);a.add_argument('--resume',action='store_true');a.add_argument('--jobs',type=int,default=16)
    x=a.parse_args();need(sum(v is not None for v in[x.prepare,x.run,x.verify,x.check])==1,'exactly one route')
    if x.prepare:m=prepare(x.prepare);print(json.dumps(dict(status='PREPARED_NOT_LAUNCHED',modules=len(m['modules']))))
    if x.check:m=manifest(x.check.resolve());print(json.dumps(dict(status='PREFLIGHT_PASS_NO_COMPILERS',modules=len(m['modules']))))
    if x.run:run(x.run,x.jobs,x.resume)
    if x.verify:r=validate(x.verify.resolve());print(r['status'])
if __name__=='__main__':main()
