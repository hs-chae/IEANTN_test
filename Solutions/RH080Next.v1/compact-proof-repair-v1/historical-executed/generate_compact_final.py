#!/usr/bin/env python3
"""Source-only proof engineering: preserve the pinned FFT math and concrete data.
Two proof bodies use already checked symbolic list lemmas. No numerical algorithm changes.
"""
import argparse, hashlib, json, os, re, tempfile
from pathlib import Path
EXPECTED = {13: '140018a66af046da2a0dd21078e38991fb0f320e5189a64035e707ccabce5c6d',
            24: '0580d2758c2908eb496518bf654df17163736019f4bfdeadad8dafa99df4da69'}
HELPERS = {'TopShapeSymbolic.lean': '121b1b44651f312abf569164f5117fe33ffb18d5ab3fc4f1c6f564fafee56726',
           'NormSymbolic.lean': 'dc3590afbf7a804cc8d033db03dbdda826f4575f6d2f59755a9c97d43500b333'}


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def digest(s):
    return hashlib.sha256(s.encode()).hexdigest()


def publish(p, value):
    fd, tmp = tempfile.mkstemp(prefix='.receipt-', dir=p.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, indent=2, allow_nan=False)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.link(tmp, p)
    finally:
        Path(tmp).unlink()


def declarations(text):
    lines = text.splitlines(keepends=True)
    starts = [(i, m[2]) for i, line in enumerate(lines)
              if (m := re.match(r'^(def|theorem) ([A-Za-z][A-Za-z0-9_]*)\b', line))]
    result = {}
    for i, (start, name) in enumerate(starts):
        stop = starts[i + 1][0] if i + 1 < len(starts) else len(lines)
        chunk = ''.join(lines[start:stop]).split('#print axioms', 1)[0]
        chunk = re.sub(r'\nend [^\n]+\s*$', '\n', chunk).rstrip() + '\n'
        need(name not in result and ':=' in chunk.splitlines()[0], 'Unsupported original syntax')
        result[name] = chunk
    return result


def marker(message):
    return ('run_cmd do\n'
            '  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with\n'
            '  | none => pure ()\n'
            '  | some path =>\n'
            '    let handle ← IO.FS.Handle.mk path .append\n'
            '    handle.putStrLn ' + json.dumps(message) + '\n'
            '    handle.flush\n')


def unparenthesize(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        depth = 0
        for i, c in enumerate(s):
            depth += (c == '(') - (c == ')')
            if depth == 0:
                break
        if i != len(s) - 1:
            break
        s = s[1:-1].strip()
    return s


def left_append_parts(s):
    s = unparenthesize(s)
    depth = 0
    split = None
    for i, c in enumerate(s):
        depth += (c == '(') - (c == ')')
        if depth == 0 and s[i:i+4] == ' ++ ':
            need(split is None, 'Ambiguous append expression')
            split = i
    if split is None:
        return s, []
    first, parts = left_append_parts(s[:split])
    return first, parts + [s[split+4:]]


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--stage', type=int, choices=[13, 24], required=True)
    ap.add_argument('--original-final', type=Path, required=True)
    ap.add_argument('--original-audit', type=Path, required=True)
    ap.add_argument('--helper-dir', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    need(not os.path.lexists(a.out), 'Fresh proof-source destination required')
    need(sha(a.original_final) == EXPECTED[a.stage], 'Original numerical Final source changed')
    source = a.original_final.read_text()
    audit = a.original_audit.read_text()
    blocks = declarations(source)
    need(len(blocks) == a.stage + 7, 'Original declaration inventory differs')
    need(len(declarations(audit)) == a.stage + 5, 'Original typed claim inventory differs')
    original_imports = re.findall(r'^import (\S+)$', source, re.M)
    first, siblings = left_append_parts(blocks['topTail'].split(':=', 1)[1])
    first_word = f'W4D{a.stage}W{a.stage}G0.w0'
    need(first == first_word + '.tail' and len(siblings) == (3 if a.stage == 13 else 10),
         'Original left-spine shape differs')
    rs = ',\n    '.join(siblings)
    new_shape = (blocks['top_shape'].split(':=', 1)[0] + ':= by\n' +
        '  let rs : List (List CInt) := [' + rs + ']\n' +
        '  let C : List CInt → List CInt := fun l => rs.foldl (fun left right => left ++ right) l\n' +
        f'  have hh : {first_word} = (unit,0) :: {first_word}.tail := by rfl\n' +
        '  calc\n' + f'    w{a.stage} = C {first_word} := by rfl\n' +
        f'    _ = C ((unit,0) :: {first_word}.tail) := congrArg C hh\n' +
        f'    _ = (unit,0) :: C {first_word}.tail :=\n' +
        f'      RH080Next.PrivateTopShape.appendFold_cons (unit,0) {first_word}.tail rs\n' +
        '    _ = (unit,0) :: topTail := by rfl\n')
    total = re.search(r'absSum output=(\d+)', blocks['total_checked'])[1]
    quad = re.search(r'W4\.quad=(\d+)', blocks['quad_checked'])[1]
    new_numerator = (blocks['numerator_checked'].split(':=', 1)[0] + ':= by\n' +
        f'  exact (RH080Next.PrivateNormProof.normFromOutput_of_totals {2**a.stage} output\n' +
        f'    {total} {quad}\n' +
        '    total_checked quad_checked).trans (by decide +kernel)\n')
    replacements = {'top_shape': new_shape, 'numerator_checked': new_numerator}
    identities = []
    for name, old in blocks.items():
        new = replacements.get(name, old)
        need(old.split(':=', 1)[0] == new.split(':=', 1)[0], 'Public statement changed')
        need(source.count(old) == 1, 'Original declaration not uniquely located')
        source = source.replace(old, marker(f'COMPACT_BEGIN W4DAG{a.stage}.{name}') +
                                new + marker(f'COMPACT_END W4DAG{a.stage}.{name}'), 1)
        identities.append(dict(name=f'W4DAG{a.stage}.{name}',
            header=old.split(':=', 1)[0], header_sha256=digest(old.split(':=', 1)[0]),
            original_block_sha256=digest(old), new_block_sha256=digest(new),
            body_byte_identical=(old == new)))
    source = 'import TopShapeSymbolic\nimport NormSymbolic\n' + source
    need(not re.search(r'^\s*(?:axiom|opaque|sorry|admit)\b|\bnative_decide\b', source, re.M),
         'Forbidden new proof construct')
    a.out.mkdir()
    modules = []
    probe = a.out / f'W4D{a.stage}FinalImportsProbe.lean'
    probe.write_text(''.join('import ' + n + '\n' for n in original_imports) +
                     marker(f'COMPACT_IMPORT_ONLY_PASS W4DAG{a.stage} original_import_union'))
    modules.append(dict(module=probe.stem, file=probe.name, sha256=sha(probe),
                        imports=original_imports, public_declarations=[]))
    for filename, expected in HELPERS.items():
        p = a.helper_dir / filename
        need(sha(p) == expected, 'Previously checked generic helper differs')
        target = a.out / filename
        target.write_bytes(p.read_bytes())
        imports = re.findall(r'^import (\S+)$', target.read_text(), re.M)
        modules.append(dict(module=target.stem, file=filename, sha256=expected,
                            imports=imports, public_declarations=[]))
    final = a.out / f'W4D{a.stage}Final.lean'
    final.write_text(source)
    modules.append(dict(module=final.stem, file=final.name, sha256=sha(final),
                        imports=['TopShapeSymbolic', 'NormSymbolic', *original_imports],
                        public_declarations=[r['name'] for r in identities]))
    target = a.out / f'W4D{a.stage}ClaimAudit.lean'
    target.write_bytes(a.original_audit.read_bytes())
    modules.append(dict(module=target.stem, file=target.name, sha256=sha(target),
                        imports=[final.stem], public_declarations=[
                            f'W4ClaimAudit{a.stage}.{n}' for n in declarations(audit)]))
    publish(a.out / 'ASSEMBLY.json', dict(
        status='PREPARED_PRIVATE_COMPACT_PROOF_ONLY_NOT_ACCEPTED', stage=a.stage,
        generator_sha256=sha(Path(__file__)), original_Final_source=str(a.original_final),
        original_Final_sha256=sha(a.original_final), original_ClaimAudit_source=str(a.original_audit),
        original_ClaimAudit_sha256=sha(a.original_audit), modules=modules,
        declaration_identity=identities, proof_only_changed_declarations=['top_shape','numerator_checked'],
        same_public_FQ_names_and_type_headers=True,
        all_other_bodies_byte_unchanged=True, original_typed_audit_byte_unchanged=True,
        all_original_final_print_axioms_preserved=True,
        numerical_data_C_algorithms_parameters_and_mathematical_results_unchanged=True,
        same_original_analytic_assumptions=True, new_unverified_axioms_sorry_native=False,
        original_left_append_spine_siblings=len(siblings),
        source_cold_claimed=False, new_source_first_PV_claimed=False))
    print(json.dumps(dict(stage=a.stage, modules=len(modules),
        assembly_sha256=sha(a.out / 'ASSEMBLY.json'), Final_sha256=sha(final))))


if __name__ == '__main__':
    main()
