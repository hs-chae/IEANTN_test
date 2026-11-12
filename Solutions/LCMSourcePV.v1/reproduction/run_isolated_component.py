# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: OpenAI (Codex)
# Reuse the unchanged original offline IEANTN namespace helper.
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path
S=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--component',choices=['witness','primecover'],required=True);ap.add_argument('--capsule',type=Path,required=True);ap.add_argument('--environment',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--jobs',type=int,default=8);ap.add_argument('--preflight',action='store_true');a=ap.parse_args();source=a.capsule.resolve();out=a.out.resolve();need(not out.exists()and source not in out.parents and source!=out,'fresh output outside source required');need(1<=a.jobs<=32,'jobs range');e=json.loads(a.environment.read_text());lock=json.loads((source/'SOURCE_LOCK.json').read_text());need(sha(Path(e['compiler']))==lock['compiler_sha256']and sha(Path(e['clang']))==lock['clang_sha256'],'compiler identity');need({x['name']:x['revision']for x in e['generic_dependencies']}=={x['name']:x['revision']for x in lock['generic_dependencies']},'exact component generic pins')
 out.mkdir(parents=True);work=out/'work';(work/'tmp').mkdir(parents=True);root=out/'namespace-root';root.mkdir();entries=[dict(kind='ro',path='/task',source=str(source)),dict(kind='ro',path='/runner',source=str(S)),dict(kind='rw',path='/work',source=str(work)),dict(kind='dir',path='/home/worker'),dict(kind='ro',path='/usr',source='/usr'),dict(kind='ro',path='/lib/x86_64-linux-gnu',source='/usr/lib/x86_64-linux-gnu'),dict(kind='ro',path='/lib64/ld-linux-x86-64.so.2',source='/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2'),dict(kind='ro',path='/bin/sh',source='/usr/bin/dash'),dict(kind='ro',path='/bin/bash',source='/usr/bin/bash'),dict(kind='ro',path='/opt/lean',source=str(Path(e['compiler']).parent.parent)),dict(kind='ro',path='/opt/clang',source=str(Path(e['clang']).parent.parent))];inside=dict(e,compiler='/opt/lean/bin/lean',clang='/opt/clang/bin/clang',toolchain='/opt/lean',generic_dependencies=[])
 for row in e['generic_dependencies']:
  name=row['name'];src='/generic-src/'+name;lib='/generic-lib/'+name;entries.append(dict(kind='ro',path=src,source=row['path']))
  if Path(row['library']).is_dir():entries.append(dict(kind='ro',path=lib,source=row['library']))
  inside['generic_dependencies'].append(dict(row,path=src,library=lib,sandbox=lib))
 env=out/'INSIDE_ENVIRONMENT.json';env.write_text(json.dumps(inside,indent=2)+'\n');entries.append(dict(kind='ro',path='/generic/ENVIRONMENT.json',source=str(env)));spec=dict(version=1,root=str(root),cwd='/task',uid=os.getuid(),gid=os.getgid(),command=['/usr/bin/python3.10','-I','-B','/runner/namespace_entry.py',a.component,str(a.jobs),'yes'if a.preflight else'no'],env=dict(PATH='/opt/lean/bin:/bin:/usr/bin',LANG='C',LC_ALL='C',TMPDIR='/work/tmp',MALLOC_ARENA_MAX='4'),network='offline',tmpfsSize='256m',tmpSize='16g',entries=entries);p=out/'SPEC.json';p.write_text(json.dumps(spec,indent=2)+'\n');helper=S/'scripts/agent-sandbox.py';t=time.monotonic()
 with(out/'stdout.txt').open('wb')as so,(out/'stderr.txt').open('wb')as se:q=subprocess.run(['unshare','--user','--map-root-user','--mount','--propagation','private','--','/usr/bin/python3.10','-I','-B',str(helper),str(p)],stdout=so,stderr=se)
 need(q.returncode==0,'namespace stage failed; preserved stdout/stderr');result=json.loads((work/'NAMESPACE_PIPELINE_RECEIPT.json').read_text());need(result['status']==('PREFLIGHT_ONLY_NO_PROOFS'if a.preflight else'PASS_FRESH_SOURCE_C_AND_THREE_MODE_STRICT_OFFLINE_NAMESPACE'),'inner acceptance status');need(result['source_lock_sha256']==sha(source/'SOURCE_LOCK.json'),'source lock drift')
 d=dict(status=result['status'],component=a.component,exit_code=q.returncode,seconds=time.monotonic()-t,spec_sha256=sha(p),helper_sha256=sha(helper),runner_sha256=sha(Path(__file__)),entry_sha256=sha(S/'namespace_entry.py'),inner_receipt_sha256=sha(work/'NAMESPACE_PIPELINE_RECEIPT.json'))
 (out/'RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(d['status'])
if __name__=='__main__':main()
