#!/usr/bin/env python3
"""Fresh two-source proof append over the independently validated source712.

The new mathematical consumer is conditional on exactly RH/Perron/Nicolas/BPT.
This is ordinary kernel verification, not source-first program verification.
"""
from pathlib import Path
import argparse, importlib.util, json, math, os, re, shutil, subprocess, sys, time
H=Path(__file__).resolve().parent
R=H.parents[3]
P=R/'Solutions/RHOcticPush.v1/integration/spectral_final/reproduce.py'
spec=importlib.util.spec_from_file_location('accepted_spectral712',P)
B=importlib.util.module_from_spec(spec);spec.loader.exec_module(B)
need,sha,save=B.need,B.sha,B.save
def read(path):
    def pairs(items):
        result={}
        for key,value in items:
            need(key not in result,'duplicate JSON key')
            result[key]=value
        return result
    def finite_float(text):
        value=float(text);need(math.isfinite(value),'nonfinite JSON number');return value
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_float=finite_float,
        parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite JSON number')))
ALLOW={'propext','Classical.choice','Quot.sound'}
STATUS='PASS_FRESH_ALL_REAL_BOX_TWO_FIFTHS_COROLLARY'

def rel(mod):return Path(*mod.split('.')).with_suffix('.olean')
def sources():
    freeze=read(H/'SOURCE_FREEZE.json')
    need(len(freeze['modules'])==2,'exact scientific scope')
    for x in freeze['modules']:
        need(sha(R/x['path'])==x['sha256'],'frozen scientific source')
    return freeze['modules']

def basis(root):
    root=Path(root).resolve();rr=B.validate(root)
    maps,_=B.foundation_maps(rr['foundation']['root'])
    for row in rr['build'] if 'build' in rr else read(root/'BUILD.json')['modules']:
        mod=row['module'];obj=root/'objects'/rel(mod)
        need(mod not in maps and sha(obj)==row['object_sha256'],'source712 object identity')
        maps[mod]={'object':obj,'object_sha256':row['object_sha256']}
    need(len(maps)==712,'exact validated712 source foundation')
    return maps,B.Z.Q.P.context(),{'root':str(root),'RESULT_sha256':sha(root/'RESULT.json'),
                                  'validator_sha256':sha(P)}

def command(ctx,out,mod):
    return ['/usr/bin/prlimit','--as='+str(64<<30),'--','/usr/bin/time','-v','-o',
            str(out/(mod+'.resources')),ctx['compiler'],'--root='+str(out/'source'),'-j2',
            '-o',str(out/'objects'/rel(mod)),str(out/'source'/(mod+'.lean'))]

def validate(out,candidate=None):
    out=Path(out).resolve();rr=read(candidate or out/'RESULT.json');mods=sources()
    need(rr['status']==STATUS and rr['schema']=='RH_BOX_TWO_FIFTHS_FRESH2_V1','accepted schema')
    need(rr['controller_sha256']==sha(__file__)==sha(out/'reproduce.executed.py'),'controller identity')
    need(rr['freeze_sha256']==sha(H/'SOURCE_FREEZE.json'),'exact frozen proof inputs')
    maps,ctx,base=basis(rr['foundation']['root']);need(base==rr['foundation'],'source712 foundation')
    execution=Path(rr['execution_root']);need(execution.is_absolute(),'absolute execution identity')
    need(len(rr['build'])==2 and len(rr['probes'])==2,'all actual compiler/probe routes')
    roots=[]
    for want,got in zip(mods,rr['build']):
        mod=want['module'];src=out/'source'/(mod+'.lean');obj=out/'objects'/rel(mod)
        need(got['module']==mod and type(got['returncode']) is int and got['returncode']==0,'actual compile status')
        need(src.is_file() and obj.is_file() and not src.is_symlink() and not obj.is_symlink(),'fresh source/object')
        need(sha(src)==want['sha256']==got['source_sha256'] and sha(obj)==got['object_sha256'],'source/object association')
        need(got['command']==command(ctx,execution,mod),'exact compiler command')
        for suffix in ['stdout','stderr','resources']:
            need(sha(out/(mod+'.'+suffix))==got[suffix+'_sha256'],'compiler evidence')
        rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(out/(mod+'.stdout')).read_text(),re.S)
        expected=[x['name'] for x in want['axioms']]
        need([name for name,_ in rows]==expected,'every selected actual axiom root')
        for name,axioms in rows:
            need({x.strip()for x in axioms.split(',')if x.strip()}<=ALLOW,'nonstandard/native theorem axiom')
            roots.append(name)
        rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',(out/(mod+'.resources')).read_text())
        need(rss is not None and type(got['peak_RSS_KiB']) is int and int(rss[1])==got['peak_RSS_KiB'],'actual peak child RAM')
        maps[mod]={'object':obj,'object_sha256':got['object_sha256']}
    need(len(roots)==11 and len(set(roots))==11,'all11 printed final/source/scalar roots')
    expectedImports={'BoxClassicalScalar':['SpectralComparison','NormalizedFormula'],
                     'BoxClassicalCorollary':['BoxClassicalScalar','SpectralNetwork']}
    generic=[Path(x).resolve()for x in ctx['generic_libraries']]+[Path(ctx['compiler']).resolve().parents[1]/'lib/lean']
    allowed={x['object'].resolve():x['object_sha256']for x in maps.values()}
    for want,probe in zip(mods,rr['probes']):
        mod=want['module'];need(probe['module']==mod and type(probe['returncode'])is int and probe['returncode']==0,'actual deps status')
        need(probe['command']==[ctx['compiler'],'--root='+str(execution/'source'),'--deps',str(execution/'source'/(mod+'.lean'))],'actual deps command')
        for suffix in ['stdout','stderr']:need(sha(out/(mod+'.deps.'+suffix))==probe[suffix+'_sha256'],'deps evidence')
        resolved=set()
        for line in (out/(mod+'.deps.stdout')).read_text().splitlines():
            p=Path(line)
            if p.is_relative_to(execution):p=out/p.relative_to(execution)
            p=p.resolve();resolved.add(p)
            for name,x in maps.items():
                if p.as_posix().endswith('/'+rel(name).as_posix()):
                    need(p==x['object'].resolve(),'application masquerading as generic')
            need(any(p.is_relative_to(g)for g in generic)or(p in allowed and sha(p)==allowed[p]),'foreign application object')
        need({maps[x]['object'].resolve()for x in expectedImports[mod]}<=resolved,'omitted declared application import')
    need(type(rr['fresh_scientific_sources'])is int and rr['fresh_scientific_sources']==2 and
         type(rr['total_scoped_sources'])is int and rr['total_scoped_sources']==714,'strict source census')
    need(type(rr['peak_child_RSS_KiB'])is int and rr['peak_child_RSS_KiB']==max(x['peak_RSS_KiB']for x in rr['build']),'actual child peak summary')
    need(type(rr['observed_owned_OOM_events'])is int and rr['observed_owned_OOM_events']==0,'owned process success')
    for value in [rr['seconds'],*[row['seconds']for row in rr['build']]]:
        need(type(value)in[int,float]and math.isfinite(value)and value>=0,'finite nonnegative runtime')
    admission=rr['resource_admission']
    need(all(type(x)is int for x in admission.values())and
         admission['compiler_address_limit_bytes']==64*(1<<30)and
         admission['host_reserve_bytes']==512*(1<<30)and
         admission['MemAvailable_bytes']>=576*(1<<30)and admission['free_disk_bytes']>=1<<30,
         'strict resource admission')
    owned=sum(x.stat().st_size for x in out.rglob('*')if x.is_file()and not x.is_symlink()
              and x.name not in ['RESULT.json','CANDIDATE.json'])
    need(type(rr['owned_regular_bytes_before_result'])is int and
         rr['owned_regular_bytes_before_result']==owned,'exact owned regular-byte measurement')
    need(rr['source_first_PV_claim']is False and rr['RH_only_claim']is False,'trust/source boundaries')
    return rr

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--foundation',type=Path);p.add_argument('--out',type=Path);p.add_argument('--verify',type=Path);a=p.parse_args()
    if a.verify:
        need(a.out is None and a.foundation is None,'exclusive readback');validate(a.verify)
        print('PASS_BOX_TWO_FIFTHS_READBACK');return
    need(a.out is not None and a.foundation is not None,'foundation and fresh output required')
    out=a.out.resolve();need(not out.exists()and out.parent.is_dir(),'fresh owned namespace')
    mods=sources();maps,ctx,base=basis(a.foundation)
    available=next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:'))
    free=shutil.disk_usage(out.parent).free
    need(available>=576*(1<<30),'512GiB host reserve plus64GiB compiler cap');need(free>=(1<<30),'separate disk admission')
    out.mkdir();(out/'source').mkdir();(out/'objects').mkdir();(out/'union').mkdir()
    (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    for name,x in maps.items():
        link=out/'union'/rel(name);link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(x['object'])
    for x in mods:(out/'source'/(x['module']+'.lean')).write_bytes((R/x['path']).read_bytes())
    env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'objects'),str(out/'union'),*ctx['generic_libraries']]);env['PYTHONDONTWRITEBYTECODE']='1'
    rows=[];probes=[];start=time.monotonic()
    for x in mods:
        mod=x['module'];cmd=command(ctx,out,mod);t=time.monotonic()
        with(out/(mod+'.stdout')).open('w')as so,(out/(mod+'.stderr')).open('w')as se:
            cp=subprocess.run(cmd,cwd=out/'source',env=env,stdout=so,stderr=se)
        need(cp.returncode==0,'compiler failure:'+mod)
        row={'module':mod,'command':cmd,'returncode':cp.returncode,'seconds':time.monotonic()-t,
             'source_sha256':sha(out/'source'/(mod+'.lean')),'object_sha256':sha(out/'objects'/rel(mod))}
        for suffix in ['stdout','stderr','resources']:row[suffix+'_sha256']=sha(out/(mod+'.'+suffix))
        row['peak_RSS_KiB']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',(out/(mod+'.resources')).read_text())[1]);rows.append(row)
        print(mod,round(row['seconds'],3),flush=True)
    for x in mods:
        mod=x['module'];cmd=[ctx['compiler'],'--root='+str(out/'source'),'--deps',str(out/'source'/(mod+'.lean'))];cp=subprocess.run(cmd,cwd=out/'source',env=env,text=True,capture_output=True)
        need(cp.returncode==0,'actual deps probe');row={'module':mod,'command':cmd,'returncode':cp.returncode}
        for suffix,text in [('stdout',cp.stdout),('stderr',cp.stderr)]:
            path=out/(mod+'.deps.'+suffix);path.write_text(text);row[suffix+'_sha256']=sha(path)
        probes.append(row)
    rr={'schema':'RH_BOX_TWO_FIFTHS_FRESH2_V1','status':STATUS,'execution_root':str(out),
        'controller_sha256':sha(__file__),'freeze_sha256':sha(H/'SOURCE_FREEZE.json'),'foundation':base,
        'build':rows,'probes':probes,'seconds':time.monotonic()-start,'fresh_scientific_sources':2,
        'total_scoped_sources':714,'peak_child_RSS_KiB':max(x['peak_RSS_KiB']for x in rows),
        'observed_owned_OOM_events':0,'source_first_PV_claim':False,'RH_only_claim':False,
        'resource_admission':{'MemAvailable_bytes':available,'free_disk_bytes':free,'compiler_address_limit_bytes':64<<30,'host_reserve_bytes':512<<30},
        'owned_regular_bytes_before_result':sum(x.stat().st_size for x in out.rglob('*')if x.is_file()and not x.is_symlink()),
        'trust':'Explicit RH/Perron/Nicolas/BPT remaininputs; allnewproofs kernelchecked withStd3; pinnedgenericLean/compiler/runtime/OS/hardware trusted. NoaggregateRSSsamplingclaim.'}
    save(out/'CANDIDATE.json',rr);validate(out,out/'CANDIDATE.json');os.replace(out/'CANDIDATE.json',out/'RESULT.json');print(STATUS)
if __name__=='__main__':main()
