#!/usr/bin/env python3
"""Transport this campaign's compiled proofs without reading historical objects.

The 695 numerical data/gap objects must already have been compiled from source
and have exactly the historical object bytes. Historical dependency *pathnames*
are then aliases for those fresh objects, not imports or accepted cached files.
All 299 old arithmetic objects are explicitly excluded. The remaining 2,469
arithmetic proofs and 40 application helpers were compiled in this campaign;
their exact sources, commands, objects, logs and dependency receipts are read.
This is certificate/proof provenance, not source-first program verification.
"""
from pathlib import Path
import math
import re
import subprocess
import data_stage as D

need, sha, read, exact, rel = D.need, D.sha, D.read, D.exact, D.rel
NS = D.NS


def path_key(path):
    """Canonical lexical absolute path; never open a historical object alias."""
    path = Path(path)
    need(path.is_absolute() and '..' not in path.parts, 'absolute clean object pathname')
    return str(path)


class Hasher:
    def __init__(self):
        self.hashes = {}

    def __call__(self, path):
        path = Path(path)
        stamp = path.stat()
        key = (str(path.resolve()), stamp.st_dev, stamp.st_ino, stamp.st_size,
               stamp.st_mtime_ns, stamp.st_ctime_ns)
        if key not in self.hashes:
            self.hashes[key] = sha(path)
        return self.hashes[key]


def validate_generic(context):
    need(context['compiler_sha256'] == sha(context['compiler']), 'pinned actual Lean compiler')
    for dependency in context['generic_dependencies']:
        command = ['git', 'rev-parse', 'HEAD']
        cp = subprocess.run(command, cwd=dependency['path'], capture_output=True, text=True)
        need(cp.returncode == 0 and cp.stdout.strip() == dependency['revision'],
             'pinned generic source revision')
        need(subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'],
                            cwd=dependency['path']).returncode == 0,
             'unchanged tracked generic source')


def transport(numerical, data_plan, fresh_records, require_complete=True):
    """Read current compiled receipts, substituting only identical fresh data.

    No call to C.validate, C.manifest or the historical Study/audit is permitted
    here: those routines intentionally validate the historical 994-object bank.
    Full numerical acceptance and this new source-only transport are separate.
    """
    numerical = Path(numerical).resolve()
    need(sha(numerical/'MANIFEST.json') == D.COUNT_MANIFEST,
         'unchanged fixed numerical manifest')
    cm = read(numerical/'MANIFEST.json')
    need(cm['controller_sha256'] == D.COUNT_CONTROLLER and
         cm['mathematical_target'] == [1490000000000, 55206486339] and
         type(cm['remaining_arithmetic']) is int and cm['remaining_arithmetic'] == 2469,
         'fixed target and arithmetic universe')
    C = D.controller()
    need(sha(numerical/'recover_count.executed.py') == D.COUNT_CONTROLLER,
         'immutable actually executed count controller')
    validate_generic(cm['context'])
    origin_checkpoint = numerical/'ORIGIN_CHECKPOINT.json'
    need(sha(origin_checkpoint) == cm['prior_origin']['checkpoint_sha256'],
         'fixed same-campaign origin transport inventory')
    oc = read(origin_checkpoint)
    origin = Path(oc['origin'])
    need(origin == Path(cm['prior_origin']['root']) and
         origin == numerical.with_name('pure-count-recovery-v1'),
         'fixed same-campaign V1 source namespace')
    old_records = {q['module']: q for q in oc['records']}
    old_probes = {q['module']: q for q in oc['dependency_probes']}
    need(len(old_records) == len(oc['records']) == 528 and
         len(old_probes) == len(oc['dependency_probes']) == 528,
         'all original current-campaign reused receipt/probe identities')
    all_rows = cm['modules']
    names = [q['module'] for q in all_rows]
    need(len(set(names)) == len(names) == 2512, 'fixed unique V2 proof-source population')
    kept = [q for q in all_rows if q['kind'] not in ['final', 'consumer', 'audit']]
    arithmetic = [q for q in kept if q['kind'] == 'arithmetic']
    need(len(kept) == 2509 and len(arithmetic) == 2469, 'exact current 2469+40 source basis')
    missing = set(data_plan['missing_old_parts'])
    need({q['module'] for q in arithmetic} | missing ==
         {NS+'.Check'+format(i, '04d') for i in range(2768)} and
         not ({q['module'] for q in arithmetic} & missing),
         'all2768 disjoint exact chunks; old299 omitted')
    accepted = {}
    for q in kept:
        marker = numerical/'attempts'/q['module']/'ACCEPTED.json'
        if marker.is_file():
            row = read(marker)
            need(row['module'] == q['module'], 'exact accepted current module')
            accepted[q['module']] = row
        elif require_complete:
            raise ValueError('missing current-campaign accepted module: '+q['module'])
    if require_complete:
        nr = read(numerical/'RESULT.json')
        need(nr['status'] == 'COMPLETE_EXACT_COUNT_AND_SOURCE_MODEL_EXECUTION' and
             nr['manifest_sha256'] == D.COUNT_MANIFEST and
             nr['controller_sha256'] == D.COUNT_CONTROLLER and
             exact(nr['actual_count'], [1490000000000, 55206486339]),
             'complete prior count result, never partial status')
        need([q['module'] for q in nr['records']] == names,
             'complete exact prior compiler receipt inventory')
        nr_records = {q['module']: q for q in nr['records']}
        need(all(exact(nr_records[name], row) for name, row in accepted.items()),
             'accepted marker and complete numerical receipt agree exactly')
    else:
        nr = None
    cached_sha = Hasher()
    aliases, module_aliases, historical_aliases = {}, {}, []
    fresh = {q['module']: q for q in fresh_records}
    need(len(fresh) == len(fresh_records), 'unique fresh source compiler records')
    for name, old in D.data_inputs(cm).items():
        need(name in fresh, 'every original data/gap module freshly compiled')
        row = fresh[name]
        need(row['source_sha256'] == old['source_sha256'] and
             row['object_sha256'] == old['object_sha256'],
             'byte-identical fresh data before proof environment transport')
        fresh_path = Path(row['object'])
        need(cached_sha(fresh_path) == row['object_sha256'], 'actual source-fresh data object')
        key = path_key(old['object'])
        keys = {key, path_key(numerical/'union'/rel(name).with_suffix('.olean')),
                path_key(origin/'union'/rel(name).with_suffix('.olean'))}
        for alias in keys:
            aliases[alias] = row['object_sha256']
        module_aliases[name] = keys
        historical_aliases.append(dict(module=name, historical_path=key,
             replacement=str(fresh_path.resolve()), object_sha256=row['object_sha256']))
    for q in kept:
        name = q['module']
        if name not in accepted:
            continue
        proof = accepted[name]['proof']
        actual_object = numerical/'objects'/rel(name).with_suffix('.olean')
        need(cached_sha(actual_object) == proof['object_sha256'],
             'current-campaign source-built object identity')
        keys = {path_key(actual_object), path_key(actual_object.resolve()),
                path_key(numerical/'union'/rel(name).with_suffix('.olean'))}
        if name in old_records:
            keys.add(path_key(origin/'objects'/rel(name).with_suffix('.olean')))
            keys.add(path_key(origin/'union'/rel(name).with_suffix('.olean')))
        module_aliases[name] = keys
        for key in keys:
            need(key not in aliases or aliases[key] == proof['object_sha256'],
                 'unambiguous source-built object pathname')
            aliases[key] = proof['object_sha256']
    generic = [Path(p).resolve() for p in cm['context']['generic_libraries']]
    generic += [Path(cm['context']['compiler']).resolve().parents[1]/'lib/lean']
    records = []
    for q in kept:
        name = q['module']
        if name not in accepted:
            continue
        row = accepted[name]
        path = Path(row['receipt'])
        root = origin if name in old_records else numerical
        need(path.is_relative_to(root/'attempts'/name) and path.name == 'RECEIPT.json' and
             path.parent.name.isdigit() and not path.is_symlink(), 'owned actual compiler receipt path')
        proof = read(path)
        need(exact(proof, row['proof']) and proof['status'] == 'PASS' and
             type(proof['returncode']) is int and proof['returncode'] == 0 and
             type(proof['cpu']) is int and proof['cpu'] in range(128) and
             type(proof['seconds']) in [int, float] and math.isfinite(proof['seconds']) and
             proof['seconds'] >= 0 and type(proof['peak_RSS_bytes']) is int and
             proof['peak_RSS_bytes'] > 0, 'strict actual compiler status/resources')
        if name in old_records:
            need(exact(row, old_records[name]), 'immutable current-campaign V1 receipt')
        need(proof['module'] == name and proof['source_sha256'] == q['source_sha256'] and
             cached_sha(root/'source'/rel(name)) == q['source_sha256'] and
             cached_sha(numerical/'source'/rel(name)) == q['source_sha256'],
             'actual executed and preserved exact scientific sources')
        if q['kind'] == 'arithmetic':
            index = int(name[-4:])
            text = C.leaf_text(format(index, '04d'), index*32768,
                               min(32768, 90670946-index*32768))
            need(__import__('hashlib').sha256(text.encode()).hexdigest() == q['source_sha256'],
                 'independently regenerated unchanged balanced arithmetic proposition')
        expected_command = C.command(root, cm, q, path.parent, proof['cpu'])
        need(exact(proof['command'], expected_command), 'exact original source/compiler/AS execution')
        for suffix in ['stdout', 'stderr', 'resources.txt']:
            need(cached_sha(path.parent/suffix) == proof[suffix+'_sha256'],
                 'actual compiler stdout/stderr/resource bytes')
        text = (path.parent/'stdout').read_text()
        error = (path.parent/'stderr').read_text()
        need(not any(token in text+error for token in
                     ['sorryAx', 'Lean.ofReduceBool', 'declaration uses `sorry`']),
             'no native execution axiom or admitted proof')
        reports = C.reports(text, C.required(q), q['kind'] == 'arithmetic')
        if q['kind'] == 'bridge' and name == 'PureBalancedCheck':
            C.reports(text, C.required(q), True)
        need(exact(reports, proof['axioms']), 'actual exact empty/standard axiom reports')
        usage = (path.parent/'resources.txt').read_text()
        D.observed_wall(usage, proof['seconds'])
        match = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
        need(match is not None and proof['peak_RSS_bytes'] == int(match[1])*1024,
             'actual child high-water memory evidence')
        if name in old_records:
            probe = old_probes[name]
            probe_dir = numerical/'origin-dependencies'/name
        else:
            probe = read(path.parent/'DEPENDENCY_PROBE.json')
            probe_dir = path.parent/'dependency'
        need(probe['module'] == name and type(probe['returncode']) is int and
             probe['returncode'] == 0 and exact(probe['command'],
             [cm['context']['compiler'], '--root='+str(root/'source'), '--deps',
              str(root/'source'/rel(name))]), 'exact actually executed dependency probe')
        for suffix in ['stdout', 'stderr']:
            need(cached_sha(probe_dir/suffix) == probe[suffix+'_sha256'],
                 'actual original dependency probe log bytes')
        lines = (probe_dir/'stdout').read_text().splitlines()
        need(lines and all(x.strip() for x in lines), 'nonempty actual dependency inventory')
        found = {path_key(line) for line in lines}
        for value in found:
            path_value = Path(value)
            if value in aliases:
                continue
            need(any(path_value.is_relative_to(g) for g in generic),
                 'foreign application dependency; historical299 never allowed')
            need(not any(part in {'RamanujanPV', 'LCMSourcePV', 'RHOcticPush'}
                         for part in path_value.parts),
                 'application namespace cannot masquerade as generic library')
        for imported in q['imports']:
            if imported in module_aliases:
                need(bool(found & module_aliases[imported]),
                     'every declared actual direct application dependency present')
            elif imported in {p['module'] for p in kept} or imported in cm['basis']:
                raise ValueError('missing or disallowed source-built dependency '+imported)
        records.append(dict(module=name, source_sha256=q['source_sha256'],
             object=str((numerical/'objects'/rel(name).with_suffix('.olean')).resolve()),
             object_sha256=proof['object_sha256'], receipt=str(path), receipt_sha256=cached_sha(path),
             origin='source-built-current-campaign-V1' if name in old_records else
                    'source-built-current-campaign-V2'))
    need(not any(name in missing for name in module_aliases), 'no original299 object aliases')
    return cm, records, dict(status='PASS_TARGETED_CURRENT_SOURCE_PROOF_TRANSPORT',
         complete_current_basis=require_complete, current_source_modules=len(records),
         current_arithmetic_modules=sum(q['module'].startswith(NS+'.Check') for q in records),
         numerical_result_sha256=sha(numerical/'RESULT.json') if require_complete else None,
         manifest_sha256=D.COUNT_MANIFEST, original_historical_objects_opened=0,
         byte_identical_data_aliases=historical_aliases,
         excluded_original_arithmetic_modules=sorted(missing),
         trust='Pinned compiler/kernel/runtime and captured execution receipts; numerical checking is not PV.')
