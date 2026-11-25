#!/usr/bin/env python3
"""Audit actual Lake-built Solution types, values and transitive axiom closures.
This is local kernel bookkeeping, not official Comparator/Nanoda approval.
"""
import argparse,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from register_lake import read_json


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--lake-run',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    need(not os.path.lexists(a.out),'Fresh proof audit required')
    here=Path(__file__).resolve().parent;integration=here.parent;repository=integration.parents[2]
    manifest=read_json(integration/'LAKE_PROVIDER_MANIFEST.json');projects=manifest['solution_projects'];count=len(projects)
    result=read_json(a.lake_run/'RESULT.json');plan=read_json(a.lake_run/'PLAN.json')
    need(result['status']=='PASS_ACTUAL_ALL'+str(count)+'_REGISTERED_SOLUTION_LAKE_BUILDS'and result['all_registered_projects_completed']is True and len(result['builds'])==count and result['projects']==projects,'Complete current actual Lake run required')
    need(result['plan_sha256']==sha(a.lake_run/'PLAN.json')and result['controller_sha256']==sha(integration/'run_lake_solutions.py'),'Actual Lake producer association differs')
    need(plan['source_registration_sha256']==sha(integration/'LAKE_PROVIDER_MANIFEST.json')and plan['registrar_sha256']==sha(integration/'register_lake.py'),'Current registry association differs')
    for relative,expected in plan['files'].items():need(sha(repository/relative)==expected,'Actual Lake source changed: '+relative)
    compiler=Path(plan['compiler']);lake=Path(plan['lake']);need(sha(compiler)==plan['compiler_sha256']and sha(lake)==plan['lake_sha256'],'Compiler/Lake changed')
    a.out.mkdir(parents=True);rows=[];began=time.monotonic();total=0
    for project in projects:
        folder=repository/'Solutions'/project;config=read_json(folder/'comparator.json');roots=config['theorem_names']
        need(roots and len(roots)==len(set(roots))and all(isinstance(n,str)and re.fullmatch(r'[A-Za-z0-9_.]+',n)for n in roots),'Invalid selected theorem identities')
        need(set(config['permitted_axioms'])<={'propext','Classical.choice','Quot.sound'},'Comparator permits a nonstandard axiom')
        obj=folder/'.lake/build/lib/lean/Solution.olean';need(obj.is_file(),'Actual Solution object missing')
        object_hash=sha(obj);entry=a.out/project;entry.mkdir();source=entry/'ProofAudit.lean'
        text='import Solution\nset_option pp.proofs true\n'
        for root in roots:text+='#check '+root+'\n#print axioms '+root+'\n#print '+root+'\n'
        source.write_text(text);tf=entry/'run.time';command=['/usr/bin/time','-v','-o',str(tf),'prlimit','--as='+str(64*2**30),'--',str(lake),'env',str(compiler),'-j2','-R',str(entry),str(source)]
        env=dict(os.environ);env.pop('LEAN_PATH',None);env['LEAN_NUM_THREADS']='2';start=time.monotonic()
        with(entry/'stdout').open('wb')as out,(entry/'stderr').open('wb')as err:p=subprocess.run(command,cwd=folder,env=env,stdout=out,stderr=err)
        need(p.returncode==0,'Actual Lake Solution audit failed: '+project);output=(entry/'stdout').read_text();audits={}
        for root in roots:
            match=re.search("'"+re.escape(root)+"' depends on axioms: \\[(.*?)\\]",output,re.S);need(match is not None,'Missing transitive root audit: '+root)
            axioms={n.strip()for n in match.group(1).split(',')if n.strip()};need(axioms<={'propext','Classical.choice','Quot.sound'},'Unaccepted root axiom: '+root);audits[root]=sorted(axioms)
        need(sha(obj)==object_hash,'Solution object changed during audit')
        rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tf.read_text());need(rss is not None,'Actual audit RAM metric missing')
        rows.append(dict(project=project,command=command,returncode=p.returncode,seconds=time.monotonic()-start,maximum_rss_kib=int(rss.group(1)),theorem_axioms=audits,
            object_path=str(obj.relative_to(repository)),object_sha256=object_hash,solution_source_sha256=sha(folder/'Solution.lean'),comparator_sha256=sha(folder/'comparator.json'),
            audit_source_sha256=sha(source),stdout_sha256=sha(entry/'stdout'),stderr_sha256=sha(entry/'stderr'),time_sha256=sha(tf)))
        total+=len(roots);print(project+' actual type/value/Std3 PASS',flush=True)
    for relative,expected in plan['files'].items():need(sha(repository/relative)==expected,'Actual build source changed during audit')
    final=dict(status='PASS_ACTUAL_LAKE_SOLUTION_TYPES_VALUES_AND_STD3_TRANSITIVE_AXIOMS',projects=projects,project_count=count,theorem_count=total,seconds=time.monotonic()-began,
        maximum_child_rss_kib=max(r['maximum_rss_kib']for r in rows),rows=rows,source_registration_sha256=sha(integration/'LAKE_PROVIDER_MANIFEST.json'),lake_result_sha256=sha(a.lake_run/'RESULT.json'),
        producer_sha256=sha(Path(__file__)),source_first_PV=False,official_Comparator_approval=False,nanoda_executed=False,
        scope='Actual ordinary Lake-built objects and their canonical roots only. Historical/analytic source parameters remain explicit in theorem types; separate source-cold and C-source-first receipts retain their own scope.')
    tmp=a.out/'RESULT.pending';tmp.write_text(json.dumps(final,indent=2)+'\n');os.link(tmp,a.out/'RESULT.json');tmp.unlink()
    print(json.dumps({k:final[k]for k in ['status','project_count','theorem_count','seconds']}))

if __name__=='__main__':main()
