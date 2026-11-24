#!/usr/bin/env python3
"""Associate delivered reader bytes with one unchanged source-bound historical run.

This CLI never imports a validator, checks proof objects, invokes a parent reader,
compiles, changes a bank or establishes mathematical/PV acceptance.
"""
import argparse, hashlib, json, math, os, stat
from pathlib import Path

HERE = Path(__file__).absolute().parent
PINS_SHA = 'ffa654d84b1245c38f36f5f3800c97b40815b5823501022c30a9578554ee7410'
C = Path('Solutions/RHOcticPush.v1/ramanujan/count-feasibility')

def need(ok, message):
    if not ok: raise ValueError(message)
def regular(path):
    path=Path(path).absolute()
    need(path.exists() and stat.S_ISREG(path.lstat().st_mode) and not path.is_symlink(),
         'regular nonsymlink file: '+str(path))
    need(all(not p.is_symlink() for p in path.parents),'nonsymlink source ancestry: '+str(path))
    return path
def sha(path): return hashlib.sha256(regular(path).read_bytes()).hexdigest()
def strict(path):
    def pairs(rows):
        out={}
        for k,v in rows:
            need(k not in out,'duplicate JSON field: '+k);out[k]=v
        return out
    def bad(value): raise ValueError('nonfinite JSON: '+value)
    def finite_float(value):
        number=float(value)
        need(math.isfinite(number),'nonfinite JSON float: '+value)
        return number
    return json.loads(regular(path).read_bytes().decode('utf-8'),object_pairs_hook=pairs,parse_constant=bad,parse_float=finite_float)
def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(exact(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b
def rel(value):
    p=Path(value);need(type(value) is str and not p.is_absolute() and '..' not in p.parts,
                      'safe declared relative source');return p

def associate(origin, delivered, run, context):
    pinpath=HERE/'SOURCE_ASSOCIATION_PINS.json'
    need(sha(pinpath)==PINS_SHA,'reviewed source-association pins')
    pins=strict(pinpath)
    need(type(pins) is dict and pins['schema']=='SOURCE_BOUND_HISTORICAL_READER_ASSOCIATION_V1',
         'source-association pin schema')
    origin,delivered,run=[Path(x).absolute() for x in [origin,delivered,run]]
    need(str(origin)==pins['original_source_root'] and origin.resolve()==origin and not origin.is_symlink(),
         'exact accepted original source root')
    need(delivered.is_dir() and delivered.resolve()==delivered and not delivered.is_symlink(),
         'delivered nonsymlink publication root')
    need(str(run)==pins['accepted_run'] and run.resolve()==run and not run.is_symlink(),
         'exact accepted historical run root')
    expected_context=origin/rel(pins['context_relative'])
    context=Path(context).absolute() if context is not None else expected_context
    need(context==expected_context,'exact original-ROOT context path')
    rows=[]
    def compare(path,digest,size=None,kind='source'):
        path=rel(str(path));a,b=origin/path,delivered/path
        aa,bb=regular(a).read_bytes(),regular(b).read_bytes()
        need(aa==bb and hashlib.sha256(aa).hexdigest()==digest and
             (size is None or len(aa)==size),kind+' byte association: '+str(path))
        rows.append(dict(path=str(path),sha256=digest,bytes=len(aa),kind=kind))
    need(len(pins['sources'])==11 and len({r['path'] for r in pins['sources']})==11,
         'all11 distinct source-owned Python providers')
    for row in pins['sources']:compare(row['path'],row['sha256'],row['bytes'],'validator')
    for row in pins['metadata']:
        compare(row['path'],row['sha256'],row['bytes'],'declared metadata/pinned reader')
        if Path(row['path']).suffix=='.json':strict(origin/row['path']);strict(delivered/row['path'])
    receipts=[]
    for row in pins['receipts']:
        need(sha(row['path'])==row['sha256'],'unchanged accepted receipt/executed copy: '+row['path'])
        receipts.append(row)
    result=strict(run/'RESULT.json');closure=strict(origin/C/'ieantn-consumer/SOURCE_CLOSURE.json')
    sources={row['path']:row['sha256'] for row in pins['sources']}
    own=str(C/'ieantn-consumer/reproduce.py')
    need(result['controller_sha256']==sources[own]==sha(run/'reproduce.executed.py') and
         result['closure_sha256']==sha(origin/C/'ieantn-consumer/SOURCE_CLOSURE.json')==sha(run/'SOURCE_CLOSURE.executed.json'),
         'actual accepted own controller and closure')
    need(closure['resource_policy_sha256']==sha(origin/C/'ieantn-consumer/RESOURCE_POLICY.json'),
         'declared resource-policy binding')
    need([r['module'] for r in closure['files']]==['IEANTN.Vocabulary.PrimeCounting','WordBytesBounded','IEANTNCountConsumer','IEANTNCountConsumerAudit'],
         'exact four-source declared consumer closure')
    for row in closure['files']:compare(row['source'],row['sha256'],kind='declared consumer source')
    for row in closure['providers']:
        path=C/'cold-foundation'/rel(row['file'])
        need(sources[str(path)]==row['sha256'],'declared cold provider pins')
    for name,digest in closure['portable_basis_pins'].items():
        need(sha(origin/C/'portable-source-run'/rel(name))==digest and
             sha(delivered/C/'portable-source-run'/rel(name))==digest,'declared portable-basis pin: '+name)
    remaining=Path(pins['remaining_root']);data=Path(pins['data_root'])
    rr=strict(remaining/'RESULT.json');rp=strict(remaining/'PLAN.json');dp=strict(data/'PLAN.json')
    need(result['basis']['kind']=='cold305' and result['basis']['root']==str(remaining) and
         result['basis']['RESULT_sha256']==sha(remaining/'RESULT.json') and
         rp['data_root']==str(data) and rp['data_plan_sha256']==sha(data/'PLAN.json'),
         'actual historical basis/plan roots and pins')
    need(dp['context']==str(context) and dp['context_sha256']==sha(context)==result['context_sha256']==
         sha(run/'GENERIC_CONTEXT.executed.json') and
         exact(strict(context),strict(run/'GENERIC_CONTEXT.executed.json')),
         'literal original-ROOT recorded context and SHA')
    need(dp['portable_source_manifest_sha256']==sha(origin/C/'portable/SOURCE_CLOSURE.json'),
         'declared portable source metadata')
    controls=strict(origin/C/'portable/CONTROLLERS.json')['controllers']
    need(type(controls) is list and len(controls)==2,'exact two declared bank controllers')
    declared={Path(x['path']).name:x['sha256'] for x in controls}
    engines=[]
    for row in pins['bank_engines']:
        actual=Path(row['actual_execution_provider']);published=rel(row['published_path'])
        need(actual==data/'engine/Solutions/Replay/scripts'/published.name,
             'actual recorded bank engine pathname')
        need(declared.get(published.name)==row['sha256']==sources[str(published)] and
             sha(actual)==sha(origin/published)==sha(delivered/published)==row['sha256'],
             'actual bank engine versus delivered/source/CONTROLLERS: '+published.name)
        engines.append(dict(actual_execution_provider=str(actual),published_path=str(published),sha256=row['sha256']))
    need(len(engines)==2,'both external bank engine providers')
    return dict(status='PASS_SOURCE_ASSOCIATION_METADATA_ONLY',accepted_source_root=str(origin),
        delivered_root=str(delivered),accepted_run=str(run),context=str(context),context_sha256=sha(context),
        source_association_helper_sha256=sha(Path(__file__).absolute()),pins_sha256=PINS_SHA,
        source_owned_python_files=11,associated_files=rows,bank_engines=engines,accepted_receipts=receipts,
        original_reader=str(origin/own),original_reader_sha256=sources[own],
        mathematical_acceptance=False,source_first_PV_acceptance=False,parent_reader_invoked=False,
        scope='Delivered-byte association for the unchanged original-location historical reader. Not relocated/portable historical verification, a full-high clean execution or mathematical acceptance.')

def main():
    p=argparse.ArgumentParser(allow_abbrev=False,description=__doc__)
    p.add_argument('--accepted-source-root',type=Path,required=True)
    p.add_argument('--delivered-root',type=Path,required=True)
    p.add_argument('--ieantn-run',type=Path,required=True)
    p.add_argument('--context',type=Path)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--out',type=Path);g.add_argument('--check-receipt',type=Path)
    a=p.parse_args()
    if a.out is not None:
        need(not a.out.exists() and not a.out.is_symlink() and a.out.parent.is_dir(),
             'fresh association receipt path')
    value=associate(a.accepted_source_root,a.delivered_root,a.ieantn_run,a.context)
    if a.check_receipt is not None:
        need(exact(strict(a.check_receipt),value),'exact source-association receipt')
        print('PASS unchanged source association receipt; no parent reader invoked');return
    temp=Path(str(a.out)+'.pending')
    need(not temp.exists() and not temp.is_symlink(),'fresh atomic association temporary')
    temp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');os.replace(temp,a.out)
    print('PASS source association metadata only; no parent reader invoked')
if __name__=='__main__':main()
