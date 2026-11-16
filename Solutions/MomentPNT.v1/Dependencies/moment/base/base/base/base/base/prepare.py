"""Freeze the exact bare768 source-point/ANT graph; never read object banks.

Maintainer snapshot tool. Clean users run reproduce.py from the resulting
source-only capsule and do not need this repository or any application objects.
"""
from pathlib import Path
import difflib
import hashlib
import importlib.util
import json
import re
import shutil

B=Path(__file__).resolve().parent
R=B.parents[1]
M=R/'research/analytic/kernel-validity-capsule-v1'
C=R/'research/source-height-capsule-v1'
def need(value,message):
    if not value:
        raise RuntimeError(message)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def copy(path,relative):
    dest=B/relative
    dest.parent.mkdir(parents=True,exist_ok=True)
    need(not dest.exists() or sha(dest)==sha(path),'immutable partial snapshot '+str(relative))
    dest.write_bytes(path.read_bytes())
    return str(relative)
def normalize_variant(text):
    text=text.replace('by native_decide','by decide +kernel')
    text=text.replace('(the Ramanujan–Soldner constant, `1.0451…`).','(the fixed value `1.0451…`).')
    options={'set_option maxHeartbeats 0','set_option maxRecDepth 100000'}
    return '\n'.join(line for line in text.splitlines() if line.strip() and line.strip() not in options)

def main():
    need(not (B/'SOURCE_LOCK.json').exists(),'new source snapshot required')
    ml=json.loads((M/'SOURCE_LOCK.json').read_text())
    cl=json.loads((C/'SOURCE_LOCK_ALL768.json').read_text())
    default=json.loads((C/'SOURCE_LOCK.json').read_text())
    need(len(ml['sources'])==463 and len(cl['sources'])==1156 and len(default['sources'])==390,'fixed original source populations')
    need(ml['compiler_sha256']==cl['compiler_sha256'] and ml['generic_dependencies']==cl['generic_dependencies']
         and ml['runtime_pins']==cl['runtime_pins'],'same pinned public compiler/libraries/runtime')
    mr={x['module']:x for x in ml['sources']}
    cr={x['module']:x for x in cl['sources']}
    same=sorted(n for n in mr.keys()&cr.keys() if mr[n]['sha256']==cr[n]['sha256'])
    changed=sorted(n for n in mr.keys()&cr.keys() if mr[n]['sha256']!=cr[n]['sha256'])
    expected=['EulerGammaBound','HeightProfileScalars','IEANTN.Vocabulary.PrimeCounting',
              'OriginalBoundaryScalars','OriginalScalars','ReversAmplitude']
    need(len(same)==231 and changed==expected,'exact original overlap/variant identities')
    variants=[]
    for name in changed:
        old=C/cr[name]['path'];new=M/mr[name]['path']
        need(sha(old)==cr[name]['sha256'] and sha(new)==mr[name]['sha256'],'variant byte identity')
        need(normalize_variant(old.read_text())==normalize_variant(new.read_text()),'only exact allowed proof/options/comment changes '+name)
        path=copy(old,Path('provenance/captured-C-source-variants')/Path(name.replace('.','/')).with_suffix('.lean'))
        diff=''.join(difflib.unified_diff(old.read_text().splitlines(True),new.read_text().splitlines(True),
                    fromfile='captured-C/'+name,tofile='selected-math-nativefree/'+name))
        dest=Path('provenance/source-diffs')/Path(name.replace('.','/')).with_suffix('.diff')
        (B/dest).parent.mkdir(parents=True,exist_ok=True)
        (B/dest).write_text(diff)
        variants.append(dict(module=name,old_source=path,old_sha256=sha(old),selected_math_sha256=sha(new),
            diff=str(dest),qualification='Only kernel proof replacement/options, or the recorded comment correction; mathematical declarations and executable data unchanged.'))
    source={n:(C/row['path'],row) for n,row in cr.items()}
    source.update({n:(M/row['path'],row) for n,row in mr.items()})
    roots=list(dict.fromkeys(ml['roots']+cl['roots']))
    root_modules=list(dict.fromkeys(ml['root_modules']+cl['root_modules']))
    extras=[]
    aggregate=R/'research/source-point-aggregate-v1/source/SourceHeightPointsV2'
    consumer=R/'research/source-pnt-consumer-v1/source/SourceHeightPointsV2'
    for p in sorted(aggregate.glob('*.lean'))+sorted(consumer.glob('*.lean')):
        name='SourceHeightPointsV2.'+p.stem
        need(name not in source,'new component module identity '+name)
        source[name]=(p,None)
        extras.append(name)
        root_modules.append(name)
    need(len(extras)==28,'24 blocks, All, PNT and two family APIs')
    roots += [f'SourceHeightPointsV2.Block{i:02d}.outputs' for i in range(24)]
    roots += ['SourceHeightPointsV2.All.outputs','SourceHeightPointsV2.PNT.source_pi_008441646',
              'SourceHeightPointsV2.PNT.source_prime_rich_017',
              'SynergyHeightC.PointExecuteAPI.family_point_bounds','SynergyHeightC.PointExecuteAPI.family_endpoint_caps',
              'SynergyHeightC.PointExecuteAPI.actual_height_caps_of_output_family',
              'SynergyHeightC.PointExecuteAPI.pi_008441646_of_output_family',
              'SynergyHeightC.PointExecuteAPI.pi_008442_of_output_family',
              'SynergyHeightC.PointExecuteAPI.prime_rich_017_of_output_family']
    scanner_spec=importlib.util.spec_from_file_location('exact_imports',R/'scoped/body43-supplement-v1/prepare_snapshot.py')
    scanner=importlib.util.module_from_spec(scanner_spec)
    scanner_spec.loader.exec_module(scanner)
    env=json.loads((R/'scoped/build/current52-public-environment-OO.json').read_text())
    generic=[Path(d['objects']) for d in env['generic_dependencies']]+[Path(env['compiler']).parent.parent/'lib/lean']
    def is_generic(name):
        rel=Path(name.replace('.','/')).with_suffix('.olean')
        return any((p/rel).is_file() for p in generic)
    additions=[]
    queue=list(source)
    cursor=0
    while cursor<len(queue):
        name=queue[cursor];cursor+=1
        path,row=source[name]
        if row is not None:
            need(sha(path)==row['sha256'],'original selected source identity '+name)
        for child in scanner.imports(path.read_text()):
            if child in source or is_generic(child):
                continue
            rel=Path(child.replace('.','/')).with_suffix('.lean')
            candidates=[p/rel for p in [R/'research/analytic/lean',R/'research/basis-source/lean',
                R/'scoped/frontend/lean',R/'scoped/stdio-v1/lean'] if (p/rel).is_file()]
            need(candidates and len({sha(p) for p in candidates})==1,'unambiguous additional actual bridge source '+child)
            source[child]=(candidates[0],None)
            queue.append(child)
            additions.append(child)
    state={};ordered=[]
    def visit(name):
        if name in state:
            need(state[name]=='done','acyclic source graph '+name)
            return
        state[name]='active'
        path,row=source[name]
        imports=[n for n in scanner.imports(path.read_text()) if n in source]
        for child in imports:
            visit(child)
        rel=Path('source')/Path(name.replace('.','/')).with_suffix('.lean')
        copy(path,rel)
        ordered.append(dict(module=name,path=str(rel),sha256=sha(path),bytes=path.stat().st_size,imports=imports))
        state[name]='done'
    for name in sorted(source):
        visit(name)
    payloads=[]
    for row in cl['payloads']:
        copy(C/row['path'],row['path'])
        payloads.append(row)
    covered={r['path']:r['sha256'] for r in cl['sources']+cl['payloads']}
    need(all(covered.get(r['path'])==r['sha256'] for r in default['sources']+default['payloads']),
         'all corrected390 source/payload bytes preserved by the all768 graph')
    original_manif=json.loads((M/'CAPSULE_FILES_V1.json').read_text())
    for row in original_manif['files']:
        if row['path'].startswith('numerics/'):
            need(sha(M/row['path'])==row['sha256'],'original numerical regeneration source pin')
            copy(M/row['path'],row['path'])
    evidence=[('research/source-pnt-consumer-v1/build-v1/RECEIPT.json','evidence/consumer/RECEIPT.json'),
        ('research/source-pnt-consumer-v1/build-v1/stdout.txt','evidence/consumer/stdout.txt'),
        ('research/source-pnt-consumer-v1/PROOF_ONLY_BANK_RECONCILIATION_V1.json','evidence/reconciliation/RECEIPT.json'),
        ('research/source-pnt-consumer-v1/CompareDeclarations.lean','evidence/reconciliation/CompareDeclarations.lean'),
        ('research/source-pnt-consumer-v1/frozen-identity-v3.stdout','evidence/reconciliation/frozen.stdout'),
        ('research/source-pnt-consumer-v1/kernel-identity-v3.stdout','evidence/reconciliation/kernel.stdout'),
        ('research/source-pnt-consumer-v1/family-api-v1/COMPILE_RECORDS.json','evidence/family/COMPILE_RECORDS.json'),
        ('research/source-pnt-consumer-v1/family-api-v1/OutputFamily.stdout','evidence/family/OutputFamily.stdout'),
        ('research/source-pnt-consumer-v1/family-api-v1/FamilyPNT.stdout','evidence/family/FamilyPNT.stdout'),
        ('research/source-point-aggregate-v1/BLOCKS_RECEIPT.json','evidence/aggregate/BLOCKS_RECEIPT.json'),
        ('research/source-point-aggregate-v1/all-v2/RECEIPT.json','evidence/aggregate/ALL_RECEIPT.json'),
        ('research/source-height-capsule-v1-cold-run-v2/RECEIPT.json','evidence/base-c390/RECEIPT.json'),
        ('research/analytic/kernel-validity-replay-v1/RECEIPT.json','evidence/base-math463/RECEIPT.json'),
        ('research/analytic/kernel-validity-replay-v1/math/RECEIPT.json','evidence/base-math463/MATH_RECEIPT.json')]
    for i in range(24):
        actual=R/f'research/source-point-aggregate-v1/block{i:02d}-v1/RECEIPT.json'
        # The accepted second block02 attempt has its own preserved receipt.
        if i==2:
            actual=R/'research/source-point-aggregate-v1/block02-v1/RECEIPT.json'
        evidence.append((str(actual.relative_to(R)),f'evidence/aggregate/Block{i:02d}.json'))
    for src,dest in evidence:
        copy(R/src,dest)
    for name in ['prepare_environment.py','reproduce_cpp.py','CPP_ASSOCIATION_PIN.json']:
        copy(C/name,name)
    copy(M/'MATHEMATICAL_CLAIM.json','MATHEMATICAL_CLAIM.json')
    copy(M/'SOURCE_LOCK.json','provenance/MATH463_SOURCE_LOCK.json')
    copy(C/'SOURCE_LOCK.json','provenance/C390_SOURCE_LOCK.json')
    copy(C/'SOURCE_LOCK_ALL768.json','provenance/C1156_SOURCE_LOCK.json')
    copy(C/'SOURCE_ASSOCIATIONS.json','provenance/C_SOURCE_ASSOCIATIONS.json')
    copy(C/'PAYLOAD_CORRECTION_V2.json','provenance/PAYLOAD_CORRECTION_V2.json')
    provenance=dict(status='EXACT_CANONICAL_SOURCE_COMPOSITION_PREPARED_NOT_REPLAYED',math_sources=463,
        C_all_point_sources=1156,byte_identical_overlaps=same,source_variants=variants,
        extra_roots=extras,additional_bridge_sources=additions,
        warm_bank_reconciliation='Nine imported object-module populations/70 declaration types and8 nonproof values; historical compatibility evidence only, not fresh source acceptance.',
        selected_source_policy='Choose native-free math source for precisely the six audited proof/comment-only variants. Preserve old variants uncompiled for provenance. Rebuild every application source from public generic libraries.',
        source_input_coverage='All corrected390-source source/payload bytes are covered by the1156 all-point source/payload graph before the six explicit proof-only source replacements.')
    (B/'COMPOSITION_PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
    lock=dict(schema='BARE768_C_SOURCE_POINT_TO_ANT_COMPOSITION_V1',compiler_sha256=ml['compiler_sha256'],
        runtime_pins=ml['runtime_pins'],generic_dependencies=ml['generic_dependencies'],sources=ordered,payloads=payloads,
        root_modules=list(dict.fromkeys(root_modules)),roots=list(dict.fromkeys(roots)),
        actual_direct_generic_import_objects=[],full_program_source_first_PV=False,combined_fresh_replay_completed=False,
        qualification='Prepared full source-only composition of the accepted math463 and C390/all768 inputs,24 aggregate blocks,All,provider-discharged PNT/prime-rich and conditional family API. Full combined fresh replay is pending. Bare-cache function-interface proof; actual initialization/main input/frame/weight/loop/I/O integration remains separate and no full-program PV is claimed.')
    need(len(lock['roots'])==2350,'exact selected mathematical/source/aggregate/family root population')
    (B/'SOURCE_LOCK.json').write_text(json.dumps(lock,indent=2)+'\n')
    print(json.dumps(dict(sources=len(ordered),payloads=len(payloads),roots=len(lock['roots']),additional_bridges=additions,
        combined_fresh_replay_completed=False)))

if __name__=='__main__':
    main()
