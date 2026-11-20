#!/usr/bin/env python3
"""Bounded ORIGINAL raw-Data stage only, reusing the audited demand controller.
No numerical Check, GapCheck, aggregate Data or count theorem is dispatched.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse, hashlib, json, os, re, subprocess, sys, time
S = Path(__file__).resolve().parents[1]
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
def need(value, message):
    if not value: raise ValueError(message)
def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): h.update(block)
    return h.hexdigest()
def read(path):
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, 'duplicate JSON key'); out[key] = value
        return out
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))
def publish(path, value):
    tmp = path.with_name(path.name + '.pending'); need(not tmp.exists(), 'fresh atomic stage')
    with tmp.open('x') as f:
        json.dump(value, f, indent=2, allow_nan=False); f.write('\n'); f.flush(); os.fsync(f.fileno())
    tmp.replace(path)
def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--manifest', type=Path, required=True); p.add_argument('--out', type=Path, required=True)
    p.add_argument('--jobs', type=int, default=2); p.add_argument('--memory-gib', type=int, default=48)
    p.add_argument('--cpus', default='0,1,2,3'); p.add_argument('--stage', choices=['raw-data'], default='raw-data')
    p.add_argument('--import-audit', type=Path, action='append', default=[])
    p.add_argument('--expected-pi', action='append', required=True, help='owner-locked N=value; repeat for every query')
    p.add_argument('--query-lock', type=Path)
    a = p.parse_args(); need(1 <= a.jobs <= 32, '1..32 independent workers')
    need(1 <= a.memory_gib <= 300 and a.jobs*a.memory_gib <= 300, 'combined worker limits <=300GiB')
    cpus = [int(x) for x in a.cpus.split(',')]
    need(len(set(cpus)) == len(cpus) and len(cpus) >= a.jobs and set(cpus) <= os.sched_getaffinity(0), 'distinct available worker CPUs')
    available = int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024
    need(available >= (512+a.jobs*a.memory_gib)*1024**3, '512GiB host reserve outside combined worker ceilings')
    if a.jobs > 4 or a.memory_gib > 48: need(available >= 1024**4, 'large pool requires genuinely available1TiB RAM')
    manifest = a.manifest.resolve(); d = read(manifest)
    need(d['schema'] == 'RAMANUJAN_PACKED_DEMAND_CERTIFICATE_PROPOSAL_V1' and d['status'] == 'UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_CHECKS', 'exact proposal schema/status')
    context = read(S/'BUILD_CONTEXT.json'); objects = Path(context['new_application_object_root']); scratch = objects.resolve().parent
    root = Path(d['source_root']).resolve(); need(root.is_relative_to(scratch), 'experiment-owned generated sources')
    names = [m['module'] for m in d['modules']]; need(len(names) == len(set(names)), 'unique module identities')
    by_name = {m['module']:m for m in d['modules']}; sources = [Path(m['source']).resolve() for m in d['modules']]
    need(len(sources) == len(set(sources)) and sorted(sources) == sorted(x.resolve() for x in root.rglob('*.lean')), 'complete written source population')
    for m, source in zip(d['modules'], sources):
        need(source.is_file() and source.is_relative_to(root) and not source.is_symlink() and sha(source) == m['sha256'], 'exact source '+m['module'])
        need(m['kind'] in ['data','check','final'], 'known source kind')
    need(len(d['queries']) == len(d['results']) and all(type(n) is int and n >= 0 for n in d['queries']), 'exact integer query population')
    need([r['N'] for r in d['results']] == d['queries'], 'every query has its own exact result')
    expected=[]
    for item in a.expected_pi:
        need(re.fullmatch(r'[0-9]+=[0-9]+', item) is not None, 'strict locked N=value')
        expected.append(tuple(map(int,item.split('='))))
    need(len(expected)==len(set(n for n,v in expected)), 'unique owner-locked queries')
    need(expected==[(r['N'],r['value']) for r in d['results']], 'exact owner-locked query/count universe')
    query_lock_path=a.query_lock
    if d['namespace']=='RamanujanPV.DemandCriticalPair':
        prescribed=S/'evidence/query-locks/CRITICAL_QUERIES.json'
        need(query_lock_path is None or query_lock_path.resolve()==prescribed.resolve(),'critical pair uses independent Root query lock')
        query_lock_path=prescribed
    query_lock=None
    if query_lock_path is not None:
        query_lock_path=query_lock_path.resolve();query_lock=read(query_lock_path)
        need(query_lock['schema']=='ieantn.ramanujan.required-critical-queries.v1','independent query-lock schema')
        need(query_lock['final_module']==d['final_module'],'locked final compiler identity')
        need([(r['N'],r['candidate_value'])for r in query_lock['required_queries']]==expected,'exact independently locked critical query universe')
        for r in query_lock['required_queries']:
            need(r['constant']==d['namespace']+'.pi_'+str(r['N']) and r['required_type']=='_root_.Nat.primeCounting '+str(r['N'])+' = '+str(r['candidate_value']),'exact locked constant and mathematical type')
        need(query_lock['required_additional_constants']==[d['namespace']+'.gaps_checked',d['namespace']+'.entries_checked'],'exact additional locked mathematical constants')
    need(sha(d['packed_file']) == d['packed_sha256'], 'complete packed-data SHA')
    compiler_hash = sha(context['compiler']); context_hash = sha(S/'BUILD_CONTEXT.json')
    scientific = {str(S/'RamanujanPV'/n):sha(S/'RamanujanPV'/n) for n in ['QuotientCertificateCode.lean','QuotientDemandCheck.lean','QuotientPartition.lean']}
    out = a.out.resolve(); need(out.is_relative_to(scratch) and out != scratch and not out.exists(), 'fresh owned execution directory')
    out.mkdir(parents=True); (out/'logs').mkdir(); started = time.monotonic()
    metadata = dict(manifest=str(manifest),manifest_sha256=sha(manifest),compiler_sha256=compiler_hash,context_sha256=context_hash,
        scientific_source_sha256=scientific,controller_sha256=sha(__file__),expected_pi=expected,query_lock=(dict(path=str(query_lock_path),sha256=sha(query_lock_path))if query_lock_path is not None else None),stage=a.stage,jobs=a.jobs,cpus=cpus[:a.jobs],
        worker_memory_limit_bytes=a.memory_gib*1024**3,combined_worker_limit_bytes=a.jobs*a.memory_gib*1024**3,
        host_memavailable_before_bytes=available,host_reserve_bytes=512*1024**3,total=len(names))
    def mandatory_names(name):
        m = by_name[name]; text = Path(m['source']).read_text()
        if m['kind'] == 'final':
            required = ['pi_'+str(r['N']) for r in d['results']]
            for r in d['results']:
                statement = 'theorem pi_'+str(r['N'])+' : Nat.primeCounting '+str(r['N'])+'='+str(r['value'])
                need(statement in text, 'exact final prime-count statement '+statement)
            return required
        if m['kind'] == 'check':
            if name.endswith('.GapCheck'): return ['gaps_checked']
            match = re.fullmatch(re.escape(d['namespace'])+r'\.Check([0-9]{4})', name)
            need(match is not None, 'exact generated chunk identity'); return ['part_'+match[1]]
        return []
    def audit_receipt(name, path):
        m = by_name[name]; path = Path(path).resolve(); need(path.is_relative_to(scratch), 'owned receipt')
        receipt = read(path); folder = path.parent
        need(receipt['status']=='COMPILED' and receipt['returncode']==0 and receipt['module']==name and receipt['source_sha256']==m['sha256'] and receipt['source_unchanged_during_compile'] is True and receipt['compiler_sha256']==compiler_hash and receipt['generic_dependency_context_sha256']==context_hash, 'actual source/compiler/context '+name)
        need(sha(folder/'source.lean')==m['sha256'], 'compiled source snapshot')
        for f,k in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]: need(sha(folder/f)==receipt[k], 'actual compiler log '+name)
        log = (folder/'stdout').read_text(); errors=(folder/'stderr').read_text()
        need(not any(v in log+errors for v in ['sorryAx','Lean.ofReduceBool','declaration uses `sorry`']), 'forbidden proof leaf '+name)
        requested = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)',Path(m['source']).read_text(),re.M)
        required = mandatory_names(name); need(set(required)<=set(requested), 'all compulsory theorem dependency reports '+name)
        for short in set(requested)|set(required):
            full=short if '.' in short else d['namespace']+'.'+short
            no = re.search(r"'"+re.escape(full)+r"' does not depend on any axioms",log)
            ax = re.search(r"'"+re.escape(full)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
            need(no is not None or ax is not None,'actual named theorem dependency report '+full)
            found=set() if no else {v.strip() for v in ax[1].split(',') if v.strip()}
            need(found<=STD3 and (m['kind']!='check' or not found),'numerical/final trust boundary '+full)
        obj=objects/Path(*name.split('.')).with_suffix('.olean')
        need(obj.is_file() and sha(obj)==receipt['object_sha256'],'exact actual compiled object '+name)
        need(sha(m['source'])==m['sha256'] and all(sha(p)==h for p,h in scientific.items()),'unchanged scientific sources')
        usage=(folder/'rusage.txt').read_text(); peak=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',usage)
        need(peak is not None,'actual peak RSS receipt')
        return dict(module=name,compiler_receipt=str(path),compiler_receipt_sha256=sha(path),source_sha256=m['sha256'],object_sha256=sha(obj),seconds=receipt['elapsed_seconds'],peak_rss_bytes=int(peak[1])*1024,mandatory_axiom_reports=required)
    metadata.update(raw_data_only=True,numeric_checks_attempted=False,prime_counts_proved_by_this_stage=False,source_first_PV=False)
    records={}
    for folder in a.import_audit:
        folder=folder.resolve();need(folder.is_relative_to(scratch),'owned imported audit tree')
        for path in sorted(folder.rglob('RUN.json')):
            prior=read(path);name=prior.get('module')
            if name in by_name and prior.get('status')=='COMPILED':
                checked=audit_receipt(name,path)
                if name in records: need(checked['object_sha256']==records[name]['object_sha256'],'consistent duplicate actual object')
                else:records[name]=checked
    done=set(records)
    for name in done: need((set(by_name[name]['dependencies'])&set(names))<=done,'all generated imported dependencies have receipts')
    target={name for name in names if by_name[name]['kind']=='data' and re.fullmatch(re.escape(d['namespace'])+r'\.Data[0-9]{4}',name)}
    expected_raw={d['namespace']+'.Data'+format(i,'04d')for i in range((d['records']+d['data_chunk']-1)//d['data_chunk'])}
    need(target==expected_raw and done<=target,'exact complete original raw-Data universe; no other imported stage')
    metadata.update(selected_raw_data_modules=sorted(target),excluded_non_raw_module_count=len(names)-len(target))
    pending=target-done;active={};idle=cpus[:a.jobs]
    def compile_one(name,cpu):
        m=by_name[name];need(sha(m['source'])==m['sha256'],'source before compiler')
        cmd=[sys.executable,*(['-'+'O'*sys.flags.optimize]if sys.flags.optimize else []),str(S/'scripts/compile_lean.py'),name,'--source-root',str(root),'--audit-root',str(out/'audit'),'--memory-gib',str(a.memory_gib),'--cpus',str(cpu)]
        result=subprocess.run(cmd,capture_output=True,text=True)
        stdout=out/'logs'/(name+'.stdout');stderr=out/'logs'/(name+'.stderr');stdout.write_text(result.stdout);stderr.write_text(result.stderr)
        need(result.returncode==0,'Lean failed '+name+'; preserved '+str(stdout))
        emitted=json.loads(result.stdout.strip().splitlines()[-1]);return audit_receipt(name,Path(emitted['audit'])/'RUN.json')
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        while pending or active:
            for name in sorted(pending):
                if not idle:break
                if (set(by_name[name]['dependencies'])&set(names))<=done:
                    cpu=idle.pop(0);active[pool.submit(compile_one,name,cpu)]=(name,cpu);pending.remove(name)
            need(active,'cyclic dependencies or incomplete imported stage')
            ready,_=wait(active,return_when=FIRST_COMPLETED)
            for future in ready:
                name,cpu=active.pop(future);idle.append(cpu);records[name]=future.result();done.add(name)
                publish(out/'PROGRESS.json',dict(metadata,status='RUNNING_OR_PARTIAL_NOT_FINAL_ACCEPTANCE',completed=len(done),last_module=name,records=list(records.values())))
    complete=done==set(names) and d['final_module'] in done
    status='COMPLETED_HOST_KERNEL_CERTIFICATE_PIPELINE_NOT_ISOLATED_NOT_C_SOURCE_PV' if complete else 'CHECKPOINT_ONLY_NOT_FINAL_ACCEPTANCE'
    final_audit=None
    if complete:
        audit_name='RamanujanPV.ControllerAudit_'+sha(manifest)[:16]
        audit_source_root=out/'controller-source';audit_source=audit_source_root/Path(*audit_name.split('.')).with_suffix('.lean');audit_source.parent.mkdir(parents=True)
        lines=['import '+d['final_module'],'open RamanujanPV.QuotientDemandCheck']
        for name in names:
            m=by_name[name]
            if m['kind']=='check':
                if name.endswith('.GapCheck'):
                    short='gaps_checked';statement='checkGaps '+d['namespace']+'.gaps '+d['namespace']+'.gapCount = true'
                else:
                    chunk=int(name.rsplit('Check',1)[1]);short='part_'+format(chunk,'04d');start=chunk*d['proof_chunk'];size=min(d['proof_chunk'],d['records']-start)
                    need(size>0,'exact complete check range')
                    statement='allFrom (checkEntry '+d['namespace']+'.nodes '+d['namespace']+'.gaps '+d['namespace']+'.gapCount) '+str(start)+' '+str(size)+' = true'
                symbol=d['namespace']+'.'+short
                lines+=['example : '+statement+' := '+symbol,'#print axioms '+symbol]
        lines+=['example : checkEntries '+d['namespace']+'.nodes '+d['namespace']+'.gaps '+d['namespace']+'.gapCount '+str(d['records'])+' = true := '+d['namespace']+'.entries_checked','#print axioms '+d['namespace']+'.entries_checked']
        for n,value in expected:
            symbol=d['namespace']+'.pi_'+str(n)
            statement='_root_.Nat.primeCounting '+str(n)+' = '+str(value)
            if query_lock is not None:
                locked=next(r for r in query_lock['required_queries']if r['N']==n);symbol=locked['constant'];statement=locked['required_type']
            lines+=['example : '+statement+' := '+symbol,'#print axioms '+symbol]
        audit_source.write_text('\n'.join(lines)+'\n')
        cmd=[sys.executable,*(['-'+'O'*sys.flags.optimize]if sys.flags.optimize else []),str(S/'scripts/compile_lean.py'),audit_name,'--source-root',str(audit_source_root),'--audit-root',str(out/'controller-audit'),'--memory-gib',str(a.memory_gib),'--cpus',str(cpus[0])]
        checked=subprocess.run(cmd,capture_output=True,text=True);(out/'controller-stdout').write_text(checked.stdout);(out/'controller-stderr').write_text(checked.stderr)
        need(checked.returncode==0,'trusted exact theorem-type/axiom audit compilation')
        emitted=json.loads(checked.stdout.strip().splitlines()[-1]);ap=Path(emitted['audit']);ar=read(ap/'RUN.json')
        need(ar['status']=='COMPILED' and ar['source_sha256']==sha(audit_source) and ar['compiler_sha256']==compiler_hash,'actual trusted audit receipt')
        log=(ap/'stdout').read_text()
        for line in lines:
            if line.startswith('#print axioms '):
                symbol=line.split()[-1];no=re.search(r"'"+re.escape(symbol)+r"' does not depend on any axioms",log);ax=re.search(r"'"+re.escape(symbol)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
                need(no is not None or ax is not None,'trusted compulsory axiom report '+symbol)
                found=set()if no else{v.strip()for v in ax[1].split(',')if v.strip()}
                numeric=symbol.rsplit('.',1)[-1].startswith(('part_','gaps_checked'))
                need(found<=STD3 and(not numeric or not found),'trusted complete theorem trust audit')
        final_audit=dict(module=audit_name,source=str(audit_source),source_sha256=sha(audit_source),receipt=str(ap/'RUN.json'),receipt_sha256=sha(ap/'RUN.json'))
    result=dict(metadata,status=status,results=d['results'],seconds=time.monotonic()-started,completed=len(done),records=list(records.values()),controller_final_theorem_audit=final_audit,remaining_boundaries='Separate actual C source/AST/execution/driver and complete mathematical consumer composition; this numerical proof is not itself source-first PV or full Ramanujan completion.')
    publish(out/'RESULT.json',result);print(json.dumps({k:result[k] for k in ['status','completed','total','seconds','results']},indent=2))
if __name__=='__main__':main()
