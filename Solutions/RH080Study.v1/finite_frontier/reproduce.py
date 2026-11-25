#!/usr/bin/env python3
"""Freshly compile the COMPLETE small finite-frontier source closure."""
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def unique(rows):
    d={}
    for k,v in rows:need(k not in d,'Duplicate JSON key');d[k]=v
    return d


def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in()).throw(ValueError(x)))


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',type=Path,required=True);ap.add_argument('--run',type=Path,required=True)
    ap.add_argument('--root',type=Path);ap.add_argument('--source-manifest',type=Path)
    a=ap.parse_args();here=Path(__file__).resolve().parent;root=a.root.resolve()if a.root else here.parent.parent.parent
    controller_hash=sha(Path(__file__));pins=read(here/'DEPENDENCY_PINS.json');context=read(a.context)
    need(all(context.get(k)==pins[k]for k in ['compiler_sha256','compiler_version','generic_dependencies']),'Pinned toolchain/generic revisions changed')
    compiler=Path(context['compiler']);need(sha(compiler)==pins['compiler_sha256'],'Compiler bytes changed')
    need(subprocess.check_output([str(compiler),'--version'],text=True).strip()==pins['compiler_version'].strip(),'Compiler version changed')
    generic=context['generic_lean_path'];generic=generic.split(':')if isinstance(generic,str)else generic
    need(isinstance(generic,list)and len(generic)==8 and all(isinstance(x,str)and Path(x).is_dir()for x in generic),'Invalid generic-only libraries')
    manifest=a.source_manifest or here/'SOURCE_MANIFEST.json';rows=read(manifest)['modules']
    names=[r['module']for r in rows];need(len(names)==len(set(names))==12,'Exact12-source closure required')
    supplied=[]
    for r in rows:
        rel=Path(r['path']);need(not rel.is_absolute()and '..'not in rel.parts,'Unsafe source path')
        p=root/rel;need(p.is_file()and sha(p)==r['sha256']and p.stat().st_size==r['bytes'],'Source bytes differ: '+r['module'])
        text=p.read_text();imports=re.findall(r'^import\s+(\S+)',text,re.M)
        need(all(x in names or x=='Mathlib'or x.startswith('Mathlib.')for x in imports),'Unexpected application import')
        need(not re.search(r'\b(sorry|admit|native_decide|ofReduceBool)\b',text),'Unaccepted source proof keyword')
        supplied.append((r,p))
    need(not os.path.lexists(a.run),'Fresh source-only run required');a.run.mkdir(parents=True)
    source=a.run/'source';objects=a.run/'objects';source.mkdir();objects.mkdir()
    for r,p in supplied:
        dst=source/(r['module'].replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(p.read_bytes())
    mem=next(int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()if l.startswith('MemAvailable:'))
    need(mem>(256+64)*2**30,'Preserve host256GiB reserve beyond per-child64GiB allowance')
    plan=dict(controller_sha256=controller_hash,manifest_sha256=sha(manifest),dependency_pins_sha256=sha(here/'DEPENDENCY_PINS.json'),
        compiler_sha256=sha(compiler),compiler_version=pins['compiler_version'],generic=generic,generic_dependencies=pins['generic_dependencies'],
        modules=rows,application_objects_supplied=False,source_only=True,per_process_AS_bytes=64*2**30,host_reserve_bytes=256*2**30,mem_available_bytes=mem)
    (a.run/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
    steps=[];began=time.monotonic();env=dict(os.environ,LEAN_PATH=':'.join([str(objects),*generic]))
    for r,_ in supplied:
        name=r['module'];rel=name.replace('.','/');out=objects/(rel+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
        log=a.run/(name+'.stdout');err=a.run/(name+'.stderr');tf=a.run/(name+'.time')
        command=['/usr/bin/time','-v','-o',str(tf),'prlimit','--as='+str(64*2**30),'--',str(compiler),'-j2','-R',str(source),'-o',str(out),str(source/(rel+'.lean'))]
        start=time.monotonic()
        with log.open('wb')as stdout,err.open('wb')as stderr:p=subprocess.run(command,env=env,stdout=stdout,stderr=stderr)
        need(p.returncode==0,'Lean source build failed: '+name)
        need('sorryAx'not in log.read_text()and 'sorryAx'not in err.read_text(),'Elaborator placeholder in completed build')
        rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tf.read_text());need(rss is not None,'Missing actual RAM')
        steps.append(dict(module=name,command=command,exit_code=p.returncode,seconds=time.monotonic()-start,maximum_rss_kib=int(rss.group(1)),
            source_sha256=sha(source/(rel+'.lean')),object_sha256=sha(out),stdout_sha256=sha(log),stderr_sha256=sha(err),time_sha256=sha(tf)))
    roots=['RH080.FiniteFrontier.'+n for n in ['closed_width1550','strict_width','strict_width1550_add','exp42_lt_four_e18','strict_log_squared','log_squared_le_iff','strict_minimum_width']]+['PrimeInterval.v5.challenge_'+n for n in ['closed_width1550','strict_width1550_add','strict_log_squared','strict_minimum_width']]
    audits='import Solution\nset_option pp.proofs true\n'
    for n in roots:audits+='#check '+n+'\n#print axioms '+n+'\n#print '+n+'\n'
    audits+='#print axioms RHOnePrimeEvolution.FiniteEndpoint.terminal_prime\n#print axioms RHOnePrime.FiniteGap.source_gap_to_terminal\n'
    audit=source/'Audit.lean';audit.write_text(audits)
    p=subprocess.run([str(compiler),'-j2','-R',str(source),str(audit)],env=env,capture_output=True)
    (a.run/'Audit.stdout').write_bytes(p.stdout);(a.run/'Audit.stderr').write_bytes(p.stderr)
    need(p.returncode==0,'Final type/value/axiom audit failed');output=p.stdout.decode();axioms={}
    for n in roots:
        m=re.search("'"+re.escape(n)+"' depends on axioms: \\[(.*?)\\]",output,re.S);need(m is not None,'Missing root axiom audit')
        ax={x.strip()for x in m.group(1).split(',')if x.strip()};need(ax<={'propext','Classical.choice','Quot.sound'},'Unaccepted root axiom');axioms[n]=sorted(ax)
    need('terminal_prime'in output and 'source_gap_to_terminal'in output and 'strict_log_squared'in output,'Missing concrete proof-value linkage')
    for r,p in supplied:need(sha(p)==r['sha256'],'Source changed during build')
    need(sha(Path(__file__))==controller_hash and sha(compiler)==pins['compiler_sha256'],'Controller/compiler changed')
    result=dict(status='PASS_COMPLETE_FRESH_SOURCE_ONLY_FINITE_FRONTIER_KERNEL_CLOSURE',seconds=time.monotonic()-began,module_count=12,steps=steps,
        maximum_child_rss_kib=max(r['maximum_rss_kib']for r in steps),oom_events=0,signal_kills=0,axiom_audits=axioms,
        audit_source_sha256=sha(audit),audit_stdout_sha256=sha(a.run/'Audit.stdout'),audit_stderr_sha256=sha(a.run/'Audit.stderr'),
        plan_sha256=sha(a.run/'PLAN.json'),source_first_PV=False,application_objects_reused=False,
        assumptions=['PrimeGapTable.v1.gaps historical1550 table, where consumed','SourceLogSquaredGap matching CMS(1.15), where consumed'],
        scope='No RH needed for these finite transfers. Terminal primality is kernel proved; historical computations remain explicit source parameters, not new axioms.')
    temp=a.run/'RESULT.json.tmp';temp.write_text(json.dumps(result,indent=2)+'\n');os.link(temp,a.run/'RESULT.json');temp.unlink()
    print(json.dumps({k:result[k]for k in ['status','seconds','module_count','maximum_child_rss_kib']}))

if __name__=='__main__':main()
