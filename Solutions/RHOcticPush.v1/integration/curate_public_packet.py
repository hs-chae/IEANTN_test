#!/usr/bin/env python3
"""Curate exactly the frozen723 source closure and needed reproduction inputs.

Selection is explicit: all723 manifest scientific files/resources/originals,
actual file-read dependencies of strict accepted723 readback/export checking,
the unchanged clean coordinator, pinned generic prerequisites, and deterministic
moment generators. No source-claim census is inferred from file-read coverage.
The default creates a source packet, not a new proof acceptance receipt.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, shutil, sys
sys.dont_write_bytecode=True
I=Path(__file__).resolve().parent
R=I.parents[2]
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(n,p):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--seed-source',required=True,type=Path)
    p.add_argument('--verified723',required=True,type=Path)
    p.add_argument('--out',required=True,type=Path)
    a=p.parse_args();seed=a.seed_source.resolve();out=a.out.resolve()
    need(seed.is_dir() and not out.exists() and not out.is_relative_to(seed),'fresh separate packet')
    opened=set()
    def hook(event,args):
        if event!='open' or not args or not isinstance(args[0],(str,bytes)):return
        try:
            q=Path(os.fsdecode(args[0])).resolve()
            if q.is_relative_to(seed) and q.is_file():opened.add(str(q.relative_to(seed)))
        except (OSError,ValueError):return
    sys.addaudithook(hook)
    exporter=load('public723exporter',seed/'Solutions/RHOcticPush.v1/integration/prepare_complete_source_packet.py')
    universe=exporter.check(seed,include_ram606=True)
    validator=load('public723validator',seed/'Solutions/RHOcticPush.v1/integration/ram606/reproduce.py')
    accepted=validator.validate(a.verified723)
    need(accepted['total_source_modules']==723,'actual accepted723')
    required=set(opened)
    explicit=[
        'LICENSE','lean-toolchain','lakefile.toml','lake-manifest.json',
        'Solutions/RHOcticPush.v1/integration/finish_clean_pipeline.py',
        'Solutions/RHOcticPush.v1/integration/prepare_complete_source_packet.py',
        'Solutions/RHOcticPush.v1/integration/README.md',
        'Solutions/RHOcticPush.v1/integration/ram606/README.md',
        'Solutions/RHOcticPush.v1/moments/endpoint/README.md',
        'Solutions/RHOcticPush.v1/moments/endpoint/SOURCE_ROOTS.json',
        'Solutions/RHOcticPush.v1/moments/endpoint/generate_endpoints.py',
        'Solutions/RHOcticPush.v1/moments/endpoint/generate_logs.py',
        'Solutions/RHOcticPush.v1/moments/endpoint/generate_cells.py',
        'Solutions/RHOcticPush.v1/moments/endpoint/generate_blocks.py',
        'Solutions/RHOcticPush.v1/moments/endpoint/generate_assembly.py']
    # Include all original fixed data/proof sources as well as their captures.
    for rel in exporter.MANIFESTS+['Solutions/RHOcticPush.v1/integration/ram606/capture/SOURCE_CLOSURE.json']:
        required.add(rel);m=json.loads((seed/rel).read_text())
        for row in m['modules']:
            required.add(row['path'])
            if row.get('original_path') is not None:required.add(row['original_path'])
        for resource in m.get('resources',[]):required.add(resource['path'])
    required.update(explicit)
    # Reproduction controllers that are invoked only on a new run are part of
    # the explicit workflow, not discoverable from readback alone.
    routes=[
        'Solutions/RHLimit.v1/scripts/reproduce_pi_complete.py',
        'Solutions/RHLimit.v1/spectral/reproduce_cold_append.py',
        'Solutions/RHLimit.v1/scripts/reproduce_integration.py',
        'Solutions/RHOcticPush.v1/integration/corrected/reproduce.py',
        'Solutions/RHOcticPush.v1/integration/supplement/reproduce.py',
        'Solutions/RHOcticPush.v1/box/zero/reproduce_zero.py',
        'Solutions/RHOcticPush.v1/integration/closed_box/reproduce.py',
        'Solutions/RHOcticPush.v1/integration/spectral_final/reproduce.py',
        'Solutions/RHOcticPush.v1/integration/ram606/reproduce.py']
    required.update(routes)
    # Current reviewed generic-prerequisite tools may postdate the immutable
    # scientific snapshot. They affect setup, not any compiler proof identity.
    additions={}
    gp=R/'Solutions/RHOcticPush.v1/ramanujan/generic-prereq'
    for name in ['preflight.py','complete.py','materialize.py','README.md','SOURCE_FREEZE.json']:
        q=gp/name;need(q.is_file(),'generic setup source');additions[str(q.relative_to(R))]=q
    additions[str(Path(__file__).resolve().relative_to(R))]=Path(__file__).resolve()
    source=out/'source';source.mkdir(parents=True)
    forbidden={'.git','.lake','__pycache__','node_modules','human_input','transcripts','private'}
    banned={'.pdf','.png','.jpg','.olean','.ilean','.o','.so','.a','.exe','.pyc'}
    rows=[]
    for rel in sorted(required|set(additions)):
        q=additions.get(rel,seed/rel)
        need(q.is_file() and not q.is_symlink(),'actual regular reproducibility input:'+rel)
        need(not (set(Path(rel).parts)&forbidden) and q.suffix not in banned,'publication exclusion:'+rel)
        data=q.read_bytes();data.decode('utf-8')
        target=source/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        rows.append({'path':rel,'sha256':sha(target),'bytes':len(data)})
    need(exporter.check(source,include_ram606=True)==universe,'exact723 relocated compiler identity')
    result={'status':'CURATED_SOURCE_EXPORT_NOT_NEW_PROOF_ACCEPTANCE','schema':'RH723_PACKET_V1',
        'file_count':len(rows),'bytes':sum(x['bytes'] for x in rows),'exact_proof_modules':723,
        'proof_universe':universe,'controller_variants':[],'clean_recovery_controller_installed':False,
        'files':rows,'curator_sha256':sha(__file__),'seed_source':str(seed),
        'source_selection':{'scientific_universe':'All723 exact manifest identities, original files and literal resources.',
            'read_dependency_universe':'Exact regular files read under the pinned source root by the complete accepted723 validator and exporter.check; actual list is independently recorded.',
            'explicit_workflow_inputs':explicit+routes,'added_setup_files':sorted(additions)},
        'publication_scope':'Selected scientific closure and necessary reproducibility inputs only; no unrelated historical snapshot, private context, papers or compiled artifacts.',
        'generic_requirements':'Pinned generic compiler and source commits remain externally installed; the included complete-cache preflight enforces selected prerequisites. No application cache is a generic prerequisite.',
        'trust':'Ordinary-kernel mathematics with explicit general literature inputs, disclosed C renderer/model contract and generic compiler/runtime/OS/hardware trust. No source-first PV or official Comparator claim.'}
    (out/'READ_DEPENDENCIES.json').write_text(json.dumps({'paths':sorted(opened),'actual_validator':str(a.verified723),'accepted_RESULT_sha256':sha(a.verified723/'RESULT.json'),'observed_scope':'Readback/export path reads, not a semantic source-claim audit.'},indent=2)+'\n')
    tmp=out/'.SOURCE_PACKET.pending';tmp.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n');os.replace(tmp,out/'SOURCE_PACKET.json')
    print(json.dumps({'status':result['status'],'files':len(rows),'bytes':result['bytes']}))
if __name__=='__main__':main()
