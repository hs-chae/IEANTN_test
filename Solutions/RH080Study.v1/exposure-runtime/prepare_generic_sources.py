#!/usr/bin/env python3
"""Regenerate exact read-only generic source views from pinned public Git trees.

No compilation/application object or account is consumed. Git metadata, caches
and untracked workspace files are excluded by git archive. Each generated tree
must match the frozen runtime's complete source-file inventory.
"""
import argparse,hashlib,importlib.util,json,os,subprocess,tarfile,tempfile
from pathlib import Path
from strict_json import read


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(2**20),b''):h.update(b)
    return h.hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--packages',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    R=a.repository.resolve(strict=True);E=R/'Solutions/RH080Study.v1/exposure-runtime';need(not a.out.exists(),'Fresh generic source output required');out=a.out.resolve();need(not out.is_relative_to(R),'Generic scratch must be outside publishable source');out.mkdir(parents=True)
    template=read(E/'references/primary.json');pin=read(E/'ADAPTER_PIN.json');gatepath=R/pin['adapter_path'];need(sha(gatepath)==pin['adapter_sha256'],'Frozen source-tree gate differs')
    spec=importlib.util.spec_from_file_location('rh080_generic_source_inventory_gate',gatepath);gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
    rows=[]
    for row in template['mounts']:
        if not row['target'].startswith('/generic/source/'):continue
        name=row['target'].rsplit('/',1)[1];package=(a.packages/name).resolve(strict=True)
        revision=subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip();need(revision==row['revision'],'Generic Git pin differs')
        need(not subprocess.check_output(['git','-C',str(package),'status','--porcelain','--untracked-files=no'],text=True),'Generic tracked source dirty')
        archive=out/(name+'.tar');command=['git','-C',str(package),'archive','--format=tar',revision]
        with archive.open('wb') as f:subprocess.run(command,stdout=f,check=True)
        target=out/name;target.mkdir()
        with tarfile.open(archive) as tar:
            for member in tar.getmembers():
                relative=Path(member.name);need(not relative.is_absolute() and '..' not in relative.parts,'Archive path outside owned package')
                need(member.isfile() or member.isdir() or member.issym(),'Unsupported generic archive member')
                if member.issym():need(not Path(member.linkname).is_absolute() and (target/relative.parent/member.linkname).resolve().is_relative_to(target),'Generic alias escapes owned source tree')
            tar.extractall(target)
        frozen=E/'references'/row['tree_file'];need(sha(frozen)==row['tree_sha256'],'Frozen source inventory differs')
        tree=read(frozen);tree['root']=str(target);manifest=out/(name+'.json');manifest.write_text(json.dumps(tree,indent=2)+'\n')
        gate.check_tree(target,dict(path=str(manifest),sha256=sha(manifest)))
        rows.append(dict(name=name,revision=revision,command=command,archive_sha256=sha(archive),generated_tree_manifest_sha256=sha(manifest),files=len(tree['files'])))
        archive.unlink()
    need(len(rows)==9,'Expected eight generic libraries plus Cli source')
    receipt=dict(status='PASS_NINE_PINNED_PUBLIC_GIT_SOURCE_VIEWS_MATCH_FROZEN_RUNTIME',packages=rows,controller_sha256=sha(Path(__file__)),application_objects_used=False,model_calls=0,temporary_archives_deleted_after_hash_check=True)
    fd,name=tempfile.mkstemp(prefix='.receipt-',dir=out);p=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(receipt,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(p,out/'RESULT.json')
    finally:p.unlink()
    print(json.dumps(dict(status=receipt['status'],packages=len(rows))))


if __name__=='__main__':main()
