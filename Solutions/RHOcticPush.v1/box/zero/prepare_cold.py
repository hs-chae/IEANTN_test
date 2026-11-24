#!/usr/bin/env python3
"""Capture exactly the frozen forty new Box moment/zero sources, never DEV objects."""
from pathlib import Path
import hashlib, json, re

H = Path(__file__).resolve().parent
S = H.parents[1]
R = S.parents[1]

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    def pairs(rows):
        out = {}
        for key, value in rows:
            need(key not in out, 'duplicate JSON key')
            out[key] = value
        return out
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))

FREEZES = [
    S/'box/gamma/SOURCE_FREEZE.json',
    S/'box/gamma/FIRST_MOMENT_SOURCE_FREEZE.json',
    S/'box/gamma/H_DERIVATIVE_SOURCE_FREEZE.json',
    S/'box/derivatives/SOURCE_FREEZE_V3.json',
    S/'box/stieltjes/SOURCE_FREEZE.json',
    H/'FINAL_ZERO_SOURCE_FREEZE.json',
]

def frozen_rows():
    out = {}
    for freeze in FREEZES:
        data = read(freeze)
        rows = data.get('modules', data.get('sources', [data]))
        for row in rows:
            source = row.get('file', row.get('path', row.get('source')))
            need(source is not None, 'source identity required')
            path = R/source
            mod = row.get('module', path.stem)
            need(mod not in out, 'duplicate compiler module identity:'+mod)
            need(sha(path) == row['sha256'], 'frozen mathematical source drift:'+mod)
            receipt = Path(row['receipt'])
            receipt = receipt if receipt.is_absolute() else R/receipt
            rc = read(receipt)
            need(rc['returncode'] == 0 and rc['source_sha256'] == row['sha256'],
                 'accepted development source receipt:'+mod)
            out[mod] = {'module': mod, 'original_path': str(path.relative_to(R)),
                        'sha256': row['sha256'], 'freeze': str(freeze.relative_to(R)),
                        'development_receipt_sha256': sha(receipt)}
    need(len(out) == 40, 'exact 40 frozen scientific modules required')
    return out

def foundation_modules():
    primary = read(S/'integration/corrected/capture/SOURCE_CLOSURE.json')
    out = set()
    for baseline in primary['baseline_manifests']:
        out.update(x['module'] for x in read(R/baseline['path'])['modules'])
    out.update(x['module'] for x in primary['modules'])
    out.update(x['module'] for x in read(
        S/'integration/supplement/audit-corrected-capture/SOURCE_CLOSURE.json')['modules'])
    need(len(out) == 619, 'exact accepted source-fresh foundation619')
    return out

def imports(path):
    # All captured imports are single physical lines. Reject unsupported alternatives.
    text = Path(path).read_text()
    need('include_str' not in text and 'include_bin' not in text,
         'new runtime resource requires an explicit capture rule')
    return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', text, re.M)

def audit_source(modules):
    lines = ['import '+m for m in modules]
    lines += ['', 'open Lean Elab Command', '',
        'theorem cold_box_zero_exact',
        '    (hN : NicolasContinuation.SourceNicolas119)',
        '    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate) :',
        '    RHSmoothingInputs.v1.box_zero_estimate :=',
        '  RHOcticPush.BoxZero.box_zero_estimate_offOrdinate hN hB', '',
        '#check @cold_box_zero_exact', '',
        'run_cmd do', '  let env ← getEnv',
        '  let mods := #['+','.join(json.dumps(m) for m in modules)+']',
        '  let allowed := #[`propext, `Classical.choice, `Quot.sound]',
        '  let mut count : Nat := 0',
        '  for (name, idx) in env.const2ModIdx.toList do',
        '    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous',
        '    if !mods.contains modName.toString then continue',
        '    let some (.thmInfo _) := env.find? name | continue',
        '    let axs ← collectAxioms name',
        '    unless axs.all allowed.contains do',
        '      throwError "Unaccepted axiom {name}: {axs}"',
        '    let row := Json.mkObj [("name",toJson name.toString),',
        '      ("module",toJson modName.toString),',
        '      ("axioms",toJson (axs.map Name.toString))]',
        '    logInfo m!"RH_BOX_ZERO_THEOREM {row.compress}"',
        '    count := count + 1',
        '  unless count > 0 do throwError "Empty forty-source audit"',
        '  let some (.thmInfo _) := env.find? `cold_box_zero_exact |',
        '    throwError "Missing exact original Box zero consumer"',
        '  let axs ← collectAxioms `cold_box_zero_exact',
        '  unless axs.all allowed.contains do throwError "Final axiom {axs}"',
        '  logInfo m!"RH_BOX_ZERO_AUDIT_PASS {count}"', '']
    return '\n'.join(lines)

def main():
    out = H/'cold-capture'
    need(not out.exists(), 'preserve existing capture; use a new explicit version')
    rows = frozen_rows()
    basis = foundation_modules()
    need(not (set(rows) & basis), 'fresh compiler namespaces required')
    ctx = read(R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
    generic = [Path(x) for x in ctx['generic_libraries']]
    generic += [Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
    for mod, row in rows.items():
        deps = imports(R/row['original_path'])
        need(deps, 'explicit imports required:'+mod)
        app = []
        for dep in deps:
            if dep in rows or dep in basis:
                app.append(dep)
            else:
                need(any((g/(dep.replace('.', '/')+'.olean')).is_file() for g in generic),
                     'application import absent from exact frozen closure:'+dep)
        row['imports'] = deps
        row['application_imports'] = app
    done = set(basis)
    ordered = []
    while rows:
        ready = sorted(m for m, row in rows.items()
                       if set(row['application_imports']) <= done)
        need(ready, 'cyclic or missing exact application import')
        for mod in ready:
            row = rows.pop(mod)
            ordered.append(row)
            done.add(mod)
    out.mkdir()
    for row in ordered:
        target = out/(row['module']+'.lean')
        target.write_bytes((R/row['original_path']).read_bytes())
        row['path'] = str(target.relative_to(R))
    audit = out/'FinalBoxZeroAudit.lean'
    audit.write_text(audit_source([x['module'] for x in ordered]))
    ordered.append({'module': 'FinalBoxZeroAudit', 'path': str(audit.relative_to(R)),
                    'original_path': None, 'sha256': sha(audit),
                    'imports': [x['module'] for x in ordered],
                    'application_imports': [x['module'] for x in ordered]})
    manifest = {'schema': 'RH_BOX_ZERO_FRESH40_CLOSURE_V1',
                'selector_sha256': sha(__file__),
                'foundation_modules': 619, 'scientific_modules': 40,
                'generated_audit_modules': 1, 'modules': ordered,
                'freezes': [{'path': str(x.relative_to(R)), 'sha256': sha(x)}
                            for x in FREEZES],
                'owned_modules': [x['module'] for x in ordered[:-1]],
                'roots': [x['module'] for x in ordered],
                'final_roots': ['RHOcticPush.BoxZero.actual_zero_average_bound',
                                'RHOcticPush.BoxZero.box_zero_estimate',
                                'RHOcticPush.BoxZero.box_zero_estimate_offOrdinate']}
    (out/'SOURCE_CLOSURE.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print('PASS_CAPTURE_EXACT40_PLUS_AUDIT')

if __name__ == '__main__':
    main()
