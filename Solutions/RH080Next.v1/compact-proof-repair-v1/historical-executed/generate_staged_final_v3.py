#!/usr/bin/env python3
"""Deterministic proof-only decomposition of the pinned integer FFT Final source.
Numerical generators, literal data, executable C, and public mathematical statements are untouched.
"""
import argparse, hashlib, json, os, re, shutil, tempfile
from pathlib import Path

D = Path('/data/ivy-rh080-next-20261125')
EXPECTED = {
    13: ('w4-fresh-unlimited-actual-controls-v1/fresh-0',
         '140018a66af046da2a0dd21078e38991fb0f320e5189a64035e707ccabce5c6d'),
    24: ('w4-dag24-kernel-nested-resume-v4-thp0-v1',
         '0580d2758c2908eb496518bf654df17163736019f4bfdeadad8dafa99df4da69'),
}
HELPER = D / 'top-shape-proof-only-20261127/TopShapeSymbolic.lean'
HELPER_SHA = '121b1b44651f312abf569164f5117fe33ffb18d5ab3fc4f1c6f564fafee56726'
BAD = re.compile(r'\bsorry\b|\badmit\b|\baxiom\s|\bnative_decide\b|Lean\.ofReduceBool')


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(2**20), b''):
            h.update(block)
    return h.hexdigest()


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def publish(path, value):
    need(not os.path.lexists(path), 'Fresh receipt required: ' + str(path))
    fd, tmp = tempfile.mkstemp(prefix='.receipt-', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, indent=2, allow_nan=False)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.link(tmp, path)
    finally:
        Path(tmp).unlink()


def declarations(text):
    lines = text.splitlines(keepends=True)
    starts = []
    for i, line in enumerate(lines):
        m = re.match(r'^(def|theorem) ([A-Za-z][A-Za-z0-9_]*)\b', line)
        if m:
            starts.append((i, m[2]))
    found = {}
    for i, (start, name) in enumerate(starts):
        stop = starts[i + 1][0] if i + 1 < len(starts) else len(lines)
        while stop > start and (lines[stop - 1].startswith('end ') or
                                lines[stop - 1].startswith('#print axioms ') or
                                not lines[stop - 1].strip()):
            stop -= 1
        chunk = ''.join(lines[start:stop])
        if '#print axioms' in chunk:
            chunk = chunk.split('#print axioms', 1)[0].rstrip() + '\n'
        need(name not in found, 'Duplicate original declaration ' + name)
        need(':=' in chunk.splitlines()[0], 'Unsupported multiline original signature ' + name)
        found[name] = chunk
    return found


def marker(message):
    return ('run_cmd do\n'
            '  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with\n'
            '  | none => pure ()\n'
            '  | some path =>\n'
            '    let handle ← IO.FS.Handle.mk path .append\n'
            '    handle.putStrLn ' + json.dumps(message) + '\n'
            '    handle.flush\n')


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--stage', type=int, choices=[13, 24], required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    need(not os.path.lexists(a.out), 'Fresh source destination required')
    bank_name, final_sha = EXPECTED[a.stage]
    bank = D / bank_name
    old_final = bank / 'sources' / f'W4D{a.stage}Final.lean'
    old_audit = bank / 'sources' / f'W4D{a.stage}ClaimAudit.lean'
    need(sha(old_final) == final_sha, 'Pinned original Final differs')
    need(sha(HELPER) == HELPER_SHA, 'Checked symbolic helper differs')
    source = old_final.read_text()
    blocks = declarations(source)
    need(len(blocks) == a.stage + 7, 'Unexpected original public declaration count')
    need(not BAD.search(source + old_audit.read_text() + HELPER.read_text()),
         'Unverified proof source construct')
    original_imports = re.findall(r'^import (\S+)$', source, re.M)
    prefix = (f'set_option autoImplicit false\nset_option Elab.async false\n'
              f'set_option maxRecDepth 2000000\nset_option maxHeartbeats 0\n'
              f'noncomputable section\nnamespace W4DAG{a.stage}\n'
              f'open RH080Next.FFT.IntegerModel\n')
    a.out.mkdir()
    rows = []
    declaration_identity = []

    def write(module, imports, names, overrides=None):
        overrides = overrides or {}
        content = ''.join('import ' + name + '\n' for name in imports) + prefix
        for name in names:
            content += marker(f'STAGED_BEGIN W4DAG{a.stage}.{name}')
            chunk = overrides.get(name, blocks[name])
            content += chunk.rstrip() + '\n'
            content += marker(f'STAGED_END W4DAG{a.stage}.{name}')
            original_header = blocks[name].split(':=', 1)[0].rstrip()
            new_header = chunk.split(':=', 1)[0].rstrip()
            need(original_header == new_header, 'Public statement changed: ' + name)
            need(name in ['top_shape', 'numerator_checked'] or chunk == blocks[name], 'Nonshape body changed')
            declaration_identity.append(dict(
                name=f'W4DAG{a.stage}.{name}', module=module,
                original_header=original_header, header_sha256=digest(original_header),
                original_block_sha256=digest(blocks[name]),
                new_block_sha256=digest(chunk),
                original_body_byte_identical=(chunk == blocks[name])))
        content += f'end W4DAG{a.stage}\n'
        p = a.out / (module + '.lean')
        p.write_text(content)
        rows.append(dict(module=module, file=p.name, sha256=sha(p), imports=imports,
                         public_declarations=[f'W4DAG{a.stage}.{n}' for n in names]))

    probe = a.out / f'W4D{a.stage}FinalImportsProbe.lean'
    probe.write_text(''.join('import ' + name + '\n' for name in original_imports) +
                     marker(f'STAGED_IMPORT_ONLY_PASS W4DAG{a.stage} original_import_union'))
    rows.append(dict(module=probe.stem, file=probe.name, sha256=sha(probe),
                     imports=original_imports, public_declarations=[]))
    shutil.copyfile(HELPER, a.out / HELPER.name)
    rows.append(dict(module='TopShapeSymbolic', file=HELPER.name,
                     sha256=HELPER_SHA, imports=['Init'], public_declarations=[]))
    norm_helper = D / 'top-shape-proof-only-20261127/NormSymbolic.lean'
    need(not BAD.search(norm_helper.read_text()), 'Forbidden generic proof source')
    shutil.copyfile(norm_helper, a.out / norm_helper.name)
    rows.append(dict(module='NormSymbolic', file=norm_helper.name,
                     sha256=sha(norm_helper), imports=['W4FFTPairedIntModel'],
                     public_declarations=[]))
    actual_shape = (D / 'top-shape-proof-only-20261127' /
                    f'TopShapeActual{a.stage}.lean').read_text()
    checked_shape = declarations(actual_shape)['top_shape']
    shape = f'W4D{a.stage}FinalShape'
    execution = f'W4D{a.stage}FinalExecution'
    twiddle = f'W4D{a.stage}FinalTwiddle'
    total = f'W4D{a.stage}FinalTotal'
    norm = f'W4D{a.stage}FinalNorm'
    write(shape, [f'W4D{a.stage}Tables', 'TopShapeSymbolic'],
          ['topTail', 'top_shape'], {'top_shape': checked_shape})
    write(execution, [f'W4D{a.stage}N{a.stage}G0'], ['output', 'complete_execution'])
    write(twiddle, [shape], ['global_twiddle_trace'])
    decimations = []
    for i in range(1, a.stage):
        module = f'W4D{a.stage}FinalDecimation{i:02d}'
        imports = [f'W4D{a.stage}Tables'] + [
            name for name in original_imports if name.startswith(f'W4D{a.stage}E{i:02d}G')]
        need(len(imports) > 1, 'Missing original decimation imports')
        write(module, imports, [f'decimation{i:02d}'])
        decimations.append(module)
    write(total, [execution], ['total_checked'])
    numeric_total = re.search(r'absSum output=(\d+)', blocks['total_checked'])[1]
    numeric_quad = re.search(r'W4\.quad=(\d+)', blocks['quad_checked'])[1]
    new_numerator = blocks['numerator_checked'].split(':=', 1)[0] + ':= by\n' + (
        f'  exact (RH080Next.PrivateNormProof.normFromOutput_of_totals {2**a.stage} output\n'
        f'    {numeric_total} {numeric_quad}\n'
        f'    total_checked quad_checked).trans (by decide +kernel)\n')
    write(norm, [total, 'NormSymbolic'], ['quad_checked', 'numerator_checked'],
          {'numerator_checked': new_numerator})
    facade = a.out / f'W4D{a.stage}Final.lean'
    facade_imports = [shape, execution, twiddle, *decimations, norm]
    facade.write_text(''.join('import ' + name + '\n' for name in facade_imports))
    rows.append(dict(module=facade.stem, file=facade.name, sha256=sha(facade),
                     imports=facade_imports, public_declarations=[]))
    target_audit = a.out / old_audit.name
    shutil.copyfile(old_audit, target_audit)
    rows.append(dict(module=target_audit.stem, file=target_audit.name,
                     sha256=sha(target_audit), imports=[facade.stem],
                     public_declarations=[f'W4ClaimAudit{a.stage}.{name}'
                                          for name in declarations(old_audit.read_text())]))
    need(set(blocks) == {r['name'].split('.')[-1] for r in declaration_identity},
         'Original public declaration coverage differs')
    need(sha(target_audit) == sha(old_audit), 'Original typed claim audit changed')
    publish(a.out / 'ASSEMBLY.json', dict(
        status='PREPARED_PRIVATE_PROOF_ONLY_STAGES_NOT_ACCEPTED', stage=a.stage,
        generator_sha256=sha(Path(__file__)), original_bank=str(bank),
        original_plan_sha256=sha(bank / 'PLAN.json'),
        original_Final_source=str(old_final), original_Final_sha256=final_sha,
        original_ClaimAudit_source=str(old_audit), original_ClaimAudit_sha256=sha(old_audit),
        modules=rows, declaration_identity=declaration_identity,
        same_public_FQ_names_and_type_headers=True,
        all_bodies_except_top_shape_and_numerator_byte_unchanged=True,
        proof_only_changed_declarations=['top_shape', 'numerator_checked'],
        original_typed_audit_byte_unchanged=True,
        numerical_data_algorithms_C_parameters_and_results_unchanged=True,
        source_cold_claimed=False, new_source_first_PV_claimed=False,
        change='Module/process decomposition plus previously kernel-checked symbolic top_shape;'
               ' abstract-output norm transfer consumes the original total and quad facts;'
               ' private file markers are diagnostics, not theorem acceptance.'))
    print(json.dumps(dict(stage=a.stage, modules=len(rows), declarations=len(blocks),
                          assembly_sha256=sha(a.out / 'ASSEMBLY.json'))))


if __name__ == '__main__':
    main()
