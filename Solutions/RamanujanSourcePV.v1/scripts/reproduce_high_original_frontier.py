#!/usr/bin/env python3
"""Regenerate the unchanged high proposal and kernel-check ONLY original chunk zero."""
from pathlib import Path
import argparse, hashlib, json, math, os, shutil, subprocess, sys, time
S = Path(__file__).resolve().parents[1]
def need(ok, message):
    if not ok: raise ValueError(message)
def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): h.update(block)
    return h.hexdigest()
def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key'); result[key] = value
        return result
    def finite(value):
        parsed=float(value); need(math.isfinite(parsed), 'nonfinite JSON float'); return parsed
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs, parse_float=finite,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))
def publish(path, value):
    stage = path.with_name(path.name + '.pending')
    with stage.open('x') as f:
        json.dump(value, f, indent=2, allow_nan=False); f.write('\n'); f.flush(); os.fsync(f.fileno())
    stage.replace(path)
def command(arguments):
    return [sys.executable, *(['-'+'O'*sys.flags.optimize] if sys.flags.optimize else []), *map(str, arguments)]
def checked_run(argv, directory, label):
    with (directory/(label+'.stdout')).open('wb') as out, (directory/(label+'.stderr')).open('wb') as err:
        result = subprocess.run(argv, stdout=out, stderr=err)
    need(result.returncode == 0, 'actual child failed: '+label)
def proposal_identity(folder, smoke):
    manifest=read(folder/'proposal/PROPOSAL.json'); lock=read(S/'evidence/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json')
    namespace='RamanujanPV.'+('HighFrontierWorkflowSmoke' if smoke else 'HighTransitionCount')
    need(manifest['schema']=='RAMANUJAN_PACKED_DEMAND_CERTIFICATE_PROPOSAL_V1' and manifest['status']=='UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_CHECKS','untrusted proposal schema')
    need(manifest['namespace']==namespace and manifest['queries']==([1000,367] if smoke else [1490000000000]),'exact query universe')
    for key in ['records','data_chunk','proof_chunk']:
        need(type(manifest[key]) is int and manifest[key]>0,'positive exact integer '+key)
    root=(folder/'proposal/source').resolve(); need(Path(manifest['source_root']).resolve()==root,'new generated source root')
    rows=manifest['modules']; need(len({r['module'] for r in rows})==len(rows),'unique generated modules')
    need({str(Path(r['source']).resolve()) for r in rows}=={str(f.resolve()) for f in root.rglob('*.lean')},'complete actual source population')
    for row in rows:
        source=Path(row['source']); need(source.resolve().is_relative_to(root) and sha(source)==row['sha256'],'actual generated source identity')
    packed=Path(manifest['packed_file']); need(packed.resolve().is_relative_to(folder/'proposal') and sha(packed)==manifest['packed_sha256'],'actual packed identity')
    source=root/Path(*namespace.split('.'))/'Check0000.lean'
    expected='theorem part_0000 : allFrom (checkEntry nodes gaps gapCount) 0 '+str(min(manifest['records'],manifest['proof_chunk']))+'=true := by decide +kernel'
    need(expected in source.read_text(),'actual exact first-chunk statement')
    if not smoke:
        for key in ['namespace','queries','records','packed_sha256','packed_bits','data_chunk','proof_chunk']:
            need(manifest[key]==lock[key],'unchanged original '+key)
        need({r['module']:r['sha256'] for r in rows}==lock['modules'],'all3464 actual original source bytes')
        need(manifest['results']==lock['original_candidates_unverified'],'unchanged original unverified candidate')
    return manifest
def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--context', type=Path, default=S/'BUILD_CONTEXT.json')
    p.add_argument('--out', type=Path)
    p.add_argument('--cpus', default='96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127')
    p.add_argument('--jobs', type=int, default=32)
    p.add_argument('--host-reserve-gib', type=int, default=512)
    p.add_argument('--smoke', action='store_true', help='small workflow control, never the original high result')
    p.add_argument('--check', type=Path)
    a = p.parse_args(); helper=S/'scripts/reproduce_profiled_closure.py'
    if a.check is not None:
        need(a.out is None and not a.smoke, 'read-only check mode')
        folder=a.check.resolve(); result=read(folder/'RESULT.json')
        need(result['status']=='REGENERATED_ORIGINAL_DATA_AND_FIRST_NUMERIC_CHUNK_ONLY' and result['mode'] in ['SMALL_WORKFLOW_CONTROL','ORIGINAL_HIGH_QUERY'], 'exact bounded result status/mode')
        need(result['controller_sha256']==sha(__file__), 'current controller identity')
        for key in ['prime_count_proved','source_first_PV','gap_check_completed','other_numeric_chunks_completed','old_application_objects_used']:
            need(result[key] is False, 'bounded trust scope '+key)
        smoke=result['mode']=='SMALL_WORKFLOW_CONTROL'; namespace='RamanujanPV.'+('HighFrontierWorkflowSmoke' if smoke else 'HighTransitionCount')
        manifest=proposal_identity(folder,smoke); lockfile=S/'evidence/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json'; lock=read(lockfile)
        need(manifest['namespace']==namespace and manifest['queries']==([1000,367] if smoke else [1490000000000]), 'exact query universe')
        need(result['selected_fact']==namespace+'.part_0000', 'only original first-chunk fact')
        need(type(result['numerical_entries_verified']) is int and result['numerical_entries_verified']==min(manifest['records'],manifest['proof_chunk']), 'exact prefix length')
        need(type(result['total_proposed_entries']) is int and result['total_proposed_entries']==manifest['records'], 'complete proposal denominator')
        need(result['original_candidate_count_unverified']==manifest['results'],'unverified candidate identity')
        if not smoke:
            for key in ['namespace','queries','records','packed_sha256','packed_bits','data_chunk','proof_chunk']:
                need(manifest[key]==lock[key], 'original proposal '+key)
            need({x['module']:x['sha256'] for x in manifest['modules']}==lock['modules'], 'all original source identities')
        context=Path(result['context_path']); need(read(context)['compiler_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', 'exact compiler pin')
        required=[Path(__file__).resolve(),S/'scripts/generate_demand_certificate_resources.py',helper,lockfile,context,folder/'proposal/PROPOSAL.json',folder/'MEMORY_PROFILES.json',folder/'replay/RESULT.json',folder/'replay/PLAN.json',folder/'generator.stdout',folder/'generator.stderr',folder/'replay.stdout',folder/'replay.stderr',folder/'readback.stdout',folder/'readback.stderr']
        need(len(result['artifacts'])==len(required) and {r['path'] for r in result['artifacts']}=={str(f) for f in required}, 'complete mandatory artifact universe')
        for record in result['artifacts']:
            need(sha(record['path'])==record['sha256'], 'artifact identity')
        subprocess.run(command([helper,'--check',folder/'replay']),check=True)
        replay=read(folder/'replay/RESULT.json')
        need(replay['axioms'][result['selected_fact']]==[], 'actual numerical fact axiom-free')
        allowed={namespace+'.Data'+format(i,'04d') for i in range((manifest['records']+manifest['data_chunk']-1)//manifest['data_chunk'])}|{namespace+'.Gaps',namespace+'.Data',namespace+'.Check0000'}
        need({r['module'] for r in replay['records'] if r['module'].startswith(namespace+'.')}==allowed, 'only first numerical check and all original data')
        print(json.dumps({'status':'CHECKED_ORIGINAL_FIRST_CHUNK_ONLY','mode':result['mode']})); return
    need(a.out is not None, 'fresh --out required'); out=a.out.resolve()
    need(not out.exists() and out.parent.is_dir(), 'fresh owned output with existing parent')
    cpus=[int(x) for x in a.cpus.split(',')]
    need(len(set(cpus))==len(cpus) and set(cpus)<=os.sched_getaffinity(0) and 1<=a.jobs<=len(cpus)<=64,'actual distinct CPUs')
    need(8<=a.host_reserve_gib<=4096,'explicit host reserve')
    memory=24 if a.smoke else 300
    available=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024
    need(available>=(a.host_reserve_gib+memory)*1024**3,'real RAM plus reserve')
    if not a.smoke:
        need(available>=1024**4 and shutil.disk_usage(out.parent).free>=1024**4,'separate genuine RAM/disk capacity')
    generator=S/'scripts/generate_demand_certificate_resources.py'; lockfile=S/'evidence/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json'; lock=read(lockfile)
    need(sha(generator)==lock['generator_sha256']=='12af93553ce0bd3a1da567f1c6e43c36c7715a67f233e1bb86dd99da2c968d81','unchanged original generator')
    out.mkdir(); started=time.monotonic(); name='HighFrontierWorkflowSmoke' if a.smoke else 'HighTransitionCount'; namespace='RamanujanPV.'+name
    queries='1000,367' if a.smoke else '1490000000000'
    generate=command([generator,'--queries',queries,'--name',name,'--out',out/'proposal','--cpus',','.join(map(str,cpus[:4])),'--memory-gib',24 if a.smoke else 256,'--max-records',300000000])
    checked_run(generate,out,'generator'); manifest=out/'proposal/PROPOSAL.json'; m=proposal_identity(out,a.smoke)
    need(m['namespace']==namespace and m['queries']==([1000,367] if a.smoke else [1490000000000]),'fixed query identities')
    if not a.smoke:
        for key in ['namespace','queries','records','packed_sha256','packed_bits','data_chunk','proof_chunk']:
            need(m[key]==lock[key],'unchanged original '+key)
        need({x['module']:x['sha256'] for x in m['modules']}==lock['modules'],'all3464 original source identities')
        need(m['results']==lock['original_candidates_unverified'],'unchanged unverified candidate')
    profile={'exact':{namespace+'.Gaps':24,namespace+'.Data':24 if a.smoke else 128,namespace+'.Check0000':24 if a.smoke else 256,'RamanujanPV.SelectedReplayAudit':24 if a.smoke else 256},'prefix':{namespace:9}}
    publish(out/'MEMORY_PROFILES.json',profile); fact=namespace+'.part_0000'
    replay=command([helper,'--context',a.context.resolve(),'--out',out/'replay','--root',namespace+'.Check0000','--theorem',fact,'--application-source-root',m['source_root'],'--memory-gib',9,'--profile-json',out/'MEMORY_PROFILES.json','--aggregate-gib',memory,'--jobs',a.jobs,'--cpus',a.cpus,'--host-reserve-gib',a.host_reserve_gib])
    checked_run(replay,out,'replay'); checked_run(command([helper,'--check',out/'replay']),out,'readback')
    result=read(out/'replay/RESULT.json'); need(result['axioms'][fact]==[],'axiom-free numerical chunk')
    allowed={namespace+'.Data'+format(i,'04d') for i in range((m['records']+m['data_chunk']-1)//m['data_chunk'])}|{namespace+'.Gaps',namespace+'.Data',namespace+'.Check0000'}
    actual={r['module'] for r in result['records'] if r['module'].startswith(namespace+'.')}
    need(actual==allowed,'all original data and ONLY first numeric check; no other checks/final')
    artifacts=[{'path':str(f),'sha256':sha(f)} for f in [Path(__file__).resolve(),generator,helper,lockfile,a.context.resolve(),manifest,out/'MEMORY_PROFILES.json',out/'replay/RESULT.json',out/'replay/PLAN.json',out/'generator.stdout',out/'generator.stderr',out/'replay.stdout',out/'replay.stderr',out/'readback.stdout',out/'readback.stderr']]
    publish(out/'RESULT.json',{'status':'REGENERATED_ORIGINAL_DATA_AND_FIRST_NUMERIC_CHUNK_ONLY','mode':'SMALL_WORKFLOW_CONTROL' if a.smoke else 'ORIGINAL_HIGH_QUERY','controller_sha256':sha(__file__),'context_path':str(a.context.resolve()),'seconds':time.monotonic()-started,'selected_fact':fact,'numerical_entries_verified':min(m['records'],m['proof_chunk']),'total_proposed_entries':m['records'],'original_candidate_count_unverified':m['results'],'prime_count_proved':False,'source_first_PV':False,'gap_check_completed':False,'other_numeric_chunks_completed':False,'old_application_objects_used':False,'commands':[generate,replay],'artifacts':artifacts})
    print(json.dumps({'status':'REGENERATED_ORIGINAL_DATA_AND_FIRST_NUMERIC_CHUNK_ONLY','mode':'SMOKE' if a.smoke else 'ORIGINAL','seconds':time.monotonic()-started}))
if __name__=='__main__': main()
