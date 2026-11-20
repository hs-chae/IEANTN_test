#!/usr/bin/env python3
"""Package exact committed source/evidence, excluding uncompiled working changes."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,tarfile,zipfile

def need(value,message):
    if not value:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def strict(data):
    def pairs(items):
        result={}
        for k,v in items:
            need(k not in result,'duplicate JSON key')
            result[k]=v
        return result
    return json.loads(data,object_pairs_hook=pairs,parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))

def verify(path):
    payloads={}
    if zipfile.is_zipfile(path):
        kind='zip'
        with zipfile.ZipFile(path) as archive:
            names=archive.namelist()
            need(len(names)==len(set(names)),'duplicate archive member')
            for name in names:
                need((archive.getinfo(name).external_attr>>16)&0o170000 != 0o120000,'symlink member')
                payloads[name]=archive.read(name)
    else:
        kind='tar.gz'
        with tarfile.open(path,'r:gz') as archive:
            members=archive.getmembers()
            names=[member.name for member in members]
            need(len(names)==len(set(names)),'duplicate archive member')
            for member in members:
                need(member.isfile(),'regular file member required')
                stream=archive.extractfile(member)
                need(stream is not None,'readable regular file')
                payloads[member.name]=stream.read()
    for name in names:
        p=Path(name)
        need(not p.is_absolute() and '..' not in p.parts and '\\' not in name,'nonlocal member')
    manifest=strict(payloads['MANIFEST.json'])
    need(manifest['schema']=='RAMANUJAN_COMMITTED_RESEARCH_BUNDLE_V1','exact schema')
    need(manifest['complete_all_real_target'] is False,'do not promote open target')
    rows=manifest['files'];need(len(rows)==len({r['path'] for r in rows}),'duplicate manifest path')
    need(set(names)=={r['path'] for r in rows}|{'MANIFEST.json'},'complete archive membership')
    for row in rows:
        payload=payloads[row['path']]
        need(len(payload)==row['bytes'] and sha(payload)==row['sha256'],'payload identity')
    return dict(status='EVERY_BUNDLE_BYTE_AND_MEMBER_VERIFIED',format=kind,files=len(rows),commit=manifest['commit'],bytes=path.stat().st_size,sha256=sha(path.read_bytes()),complete_all_real_target=False)

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--commit');p.add_argument('--out',type=Path);p.add_argument('--check',type=Path);a=p.parse_args()
    if a.check:
        need(a.commit is None and a.out is None,'separate read-only verification');print(json.dumps(verify(a.check)));return
    need(a.commit is not None and a.out is not None,'commit and fresh output required')
    s=Path(__file__).resolve().parents[1];n=s.parents[1];commit=subprocess.check_output(['git','rev-parse',a.commit+'^{commit}'],cwd=n,text=True).strip();prefix='Solutions/RamanujanSourcePV.v1/'
    entries=subprocess.check_output(['git','ls-tree','-rz',commit,'--',prefix],cwd=n).split(b'\0')
    modes={}
    for entry in entries:
        if not entry:continue
        header,name=entry.split(b'\t',1);mode,kind,_=header.split()
        need(kind==b'blob' and mode in [b'100644',b'100755'],'committed regular file')
        modes[name.decode()]=int(mode,8)&0o777
    names=list(modes);need(names,'committed solution')
    raw=subprocess.check_output(['git','cat-file','--batch'],cwd=n,input=''.join(commit+':'+name+'\n' for name in names).encode());offset=0;payloads={}
    for name in names:
        end=raw.index(b'\n',offset);header=raw[offset:end].split();need(len(header)==3 and header[1]==b'blob','committed regular blob');size=int(header[2]);offset=end+1;data=raw[offset:offset+size];offset+=size+1
        need(not any(x in name.split('/') for x in ['human_input','memory','private']),'private context exclusion');need(Path(name).suffix not in ['.pdf','.olean','.ilean','.o','.bc'],'large/research-source artifact exclusion');payloads[name]=data
    need(offset==len(raw),'exact git batch readback')
    intro='''RAMANUJAN SOURCE-FIRST PV RESEARCH — CHECKPOINT, FULL TARGET OPEN

Commit: COMMIT
Repository: https://github.com/hs-chae/IEANTN_test.git
Branch: research/ramanujan-source-first-pv-20261119

Open Solutions/RamanujanSourcePV.v1/reports/RAMANUJAN_FULL_RESEARCH_CHECKPOINT.html.
The embedded font and static MathML work offline. Read README.md and HANDOFF.md
in that same solution for exact theorem scope and remaining obligations.

This bundle contains exact committed application source and compact receipts.
It omits large deterministically regenerable datasets/proof objects and paper
PDFs. Scripts regenerate the data and compile the accepted Lean proofs. Pinned
Lean/Mathlib, native dependencies and the original network sources must be
obtained from their exact revisions. Download the full network cleanly:

  git clone https://github.com/hs-chae/IEANTN_test.git network
  git -C network checkout COMMIT

All bundled Solutions/... files must match that checkout byte-for-byte. From
network/Solutions/RamanujanSourcePV.v1, follow REPRODUCE_CRITICAL_COUNTS.md,
REPRODUCE_LOCAL_MILLION.md, REPRODUCE_FULL_SCALARS.md and FINITE_PROGRAM_README.md.
The newest complete combined clean replay may remain pending; inspect receipts,
not printed commands. The full prime-count witness has NOT been constructed.

Verify this archive using Python3 (no third-party dependencies):
  python3 Solutions/RamanujanSourcePV.v1/scripts/package_research.py --check BUNDLE.tar.gz

MANIFEST.json fixes every included file's length/hash and the exact Git commit.
No original outcome is retroactively promoted. Source-first C execution, kernel
numeric proof and ordinary native evidence remain distinct in every claim.
'''.replace('COMMIT',commit)
    payloads['START_HERE.txt']=intro.encode();modes['START_HERE.txt']=0o644
    manifest=dict(schema='RAMANUJAN_COMMITTED_RESEARCH_BUNDLE_V1',commit=commit,repository='https://github.com/hs-chae/IEANTN_test.git',complete_all_real_target=False,selection='Every tracked file under the committed RamanujanSourcePV.v1 solution, excluding paper PDFs/binary proof caches/private context; no working-tree or uncompiled agent files.',files=[dict(path=name,bytes=len(data),sha256=sha(data)) for name,data in sorted(payloads.items())])
    payloads['MANIFEST.json']=(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n').encode();modes['MANIFEST.json']=0o644;out=a.out.resolve();need(not out.exists(),'fresh archive required');out.parent.mkdir(parents=True,exist_ok=True)
    if out.name.endswith('.tar.gz'):
        import io
        with out.open('wb') as physical:
            with gzip.GzipFile(fileobj=physical,filename='',mode='wb',compresslevel=9,mtime=0) as compressed:
                with tarfile.open(fileobj=compressed,mode='w') as archive:
                    for name,data in sorted(payloads.items()):
                        info=tarfile.TarInfo(name);info.size=len(data);info.mode=modes[name];info.mtime=0
                        archive.addfile(info,io.BytesIO(data))
    else:
        need(out.suffix=='.zip','explicit .zip or .tar.gz archive')
        with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
            for name,data in sorted(payloads.items()):
                info=zipfile.ZipInfo(name,date_time=(1980,1,1,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=(0o100000|modes[name])<<16;archive.writestr(info,data,compresslevel=9)
    result=verify(out);out.with_suffix('.verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':
    main()
