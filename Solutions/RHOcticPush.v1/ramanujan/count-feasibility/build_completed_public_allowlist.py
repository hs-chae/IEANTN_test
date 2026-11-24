#!/usr/bin/env python3
"""Prepare a narrow source/evidence allowlist, not a mathematical acceptance gate.

Every scientific source is selected explicitly or by an already frozen source
manifest. External evidence is copied by exact receipt fields and hashes. No
application object, whole data bank, private handoff or source PDF is selected.
"""
from pathlib import Path
import hashlib
import json
import shutil

COUNT = Path(__file__).resolve().parent
ROOT = COUNT.parents[3]
GRAMMAR = ROOT/'Solutions/RHOcticPush.v1/finite-pv/grammar'
DATA = Path('/data/ivy-rh-octic-20261123/ramanujan')
PUBLIC = COUNT/'public-completed-v1'
ROWS = {}
COPIES = []


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs)


def add(path, purpose, expected=None):
    path = Path(path)
    need(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(ROOT),
         'owned regular public file')
    relative = str(path.relative_to(ROOT))
    need(path.suffix not in {'.olean', '.ilean', '.o', '.a', '.so', '.pdf', '.bin'} and
         not any(word in relative for word in ['__pycache__', 'ACTIVE_HANDOFF',
                                              'human_input', '/memory/', '/private/']),
         'explicit publication exclusions')
    need(path.stat().st_size <= 2_000_000, 'no bulk numerical data/source or caches')
    digest = sha(path)
    need(expected is None or digest == expected, 'exact accepted source/receipt hash:'+relative)
    if relative in ROWS:
        need(ROWS[relative]['sha256'] == digest, 'stable same-source collision')
        return
    ROWS[relative] = dict(path=relative, sha256=digest, bytes=path.stat().st_size,
                          purpose=purpose)


def copy(source, relative, purpose, expected=None):
    source = Path(source)
    need(source.is_file() and not source.is_symlink() and source.is_relative_to(DATA),
         'explicit actual evidence file')
    need(expected is None or sha(source) == expected, 'original evidence hash before copy')
    destination = PUBLIC/'evidence'/relative
    need(not destination.exists(), 'fresh immutable public evidence copy')
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    need(sha(destination) == sha(source), 'exact copied evidence bytes')
    COPIES.append(dict(original=str(source), public=str(destination.relative_to(ROOT)),
                       sha256=sha(source)))
    add(destination, purpose, sha(source))


def sources():
    # Exact self-contained fast source recipe, including all Python imports.
    import importlib.util
    path = COUNT/'portable-source-run/make_source_packet.py'
    spec = importlib.util.spec_from_file_location('exact_source_packet_selection', path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    for relative in module.paths():
        add(COUNT/relative, 'clean source-only full/small reproduction dependency')
    for name in [
        'build_completed_public_allowlist.py', 'PureBalancedCheck.lean', 'DecodedOutputs.lean',
        'HighDecodedOutputs.lean', 'HighCountSourceConsumer.lean',
        'RESOURCE_V2_SOURCE_FREEZE.json', 'ROOT_CONTROLLER_PRELAUNCH_REVIEW_V1.json',
        'ROOT_RESOURCE_V2_FINAL_REVIEW.json', 'ROOT_GENERATOR_RESOURCE_VARIANT_REVIEW.json',
        'AXIOM_CAUSE_CORRECTION.json', 'REGENERATION.json', 'GENERATOR_RESOURCE_VARIANT.json',
        'regeneration/verify_regeneration.py', 'regeneration/generate_demand_certificate_safe.py',
        'test_portable_controls.py', 'test_recovery_controls.py', 'test_recovery_v2_controls.py',
        'cold-foundation/SourceOutputAdapter.lean', 'cold-foundation/CountSourceFinal.lean.in',
        'cold-foundation/test_static.py', 'cold-foundation/INDEPENDENT_REVIEW_INITIAL_20261124.json',
        'cold-foundation/INDEPENDENT_REVIEW_FINAL_20261124.json',
        'cold-foundation/ROOT_SOURCE_CONSUMER_REVIEW.json',
        'cold-foundation/SOURCE_FREEZE_REVIEW_CANDIDATE.json',
    ]:
        add(COUNT/name, 'source or review; fixed high numerical completion remains pending')
    high = COUNT/'high-driver'
    add(high/'SOURCE_FREEZE.json', 'historical source/model freeze, numerical gate pending')
    for row in read(high/'SOURCE_FREEZE.json')['sources']:
        add(high/row['path'], 'actual high-driver source/model and reproduction', row['sha256'])
    for name in ['COMPLETE_READBACK.md', 'COMPLETE_READBACK_FREEZE.json',
                 'NATIVE_METADATA_REPAIR.json', 'FUTURE_UNION_SOURCE_COMPATIBILITY.json',
                 'readback_complete.py', 'test_readback_complete.py']:
        add(high/name, 'completed strengthened application reader and reviewed controls')
    for row in read(GRAMMAR/'REPRO_SOURCE_CLOSURE.json')['modules']:
        add(GRAMMAR/(row['module']+'.lean'), 'independent bounded C11 syntax/soundness proof', row['sha256'])
    for name in ['reproduce.py', 'reproduce_from_clean.py', 'controls.py', 'README.md',
                 'REPRO_SOURCE_CLOSURE.json', 'SOURCE_FREEZE.json',
                 'VERIFICATION_SOURCE_FREEZE.json', 'CLAIM_LEDGER.json',
                 'DECLARATION_INVENTORY.json', 'FRESH_COMPILER_THEOREM_INVENTORY.json',
                 'FRESH_REPLAY_RECEIPT.json', 'INDEPENDENT_STANDARD_REVIEW.json',
                 'HIGH_APPLICATION_READBACK_INDEPENDENT_REVIEW.json',
                 'HIGH_APPLICATION_OUTPUT_BOUNDARY_V3_INDEPENDENT_REVIEW.json',
                 'C11_SYNTAX_RECEIPT.json', 'C11_STYLE_WARNING_ATTEMPT.json',
                 'CLEANUP_RECEIPT.json', 'sources/STANDARD_LOCATORS.json',
                 'sources/STANDARD_RECEIPT.json']:
        add(GRAMMAR/name, 'completed syntax/model theorem status, primary locators or reproduction')
    for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                 'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json',
                 'Solutions/RHOcticPush.v1/integration/continuation/bootstrap_generic.py']:
        add(ROOT/name, 'generic-only clean dependency setup and exact pins')


def existing_grammar_evidence():
    fresh = GRAMMAR/'evidence/fresh5-v1'
    for name in ['RESULT.json', 'BUILD.json', 'SOURCE_CLOSURE.executed.json',
                 'RESOURCE_SAMPLES.csv', 'reproduce.executed.py']:
        add(fresh/name, 'actual accepted37-source application+grammar campaign evidence')
    for row in read(GRAMMAR/'REPRO_SOURCE_CLOSURE.json')['modules']:
        module = row['module']
        for suffix in ['stdout', 'stderr', 'resources']:
            add(fresh/'logs'/(module+'.'+suffix), 'actual fresh grammar kernel compilation log')
        for suffix in ['stdout', 'stderr']:
            add(fresh/'dependencies'/(module+'.'+suffix), 'actual fresh grammar dependency probe')
    base = GRAMMAR/'evidence/controls-v1'
    add(base/'RESULT.json', 'actual36 normal/O/OO grammar CLI control decisions')
    for row in read(base/'RESULT.json')['cases']:
        for suffix in ['stdout', 'stderr']:
            add(base/row[suffix], 'actual grammar control raw log', row[suffix+'_sha256'])


def application_evidence():
    base = DATA/'high-driver-fresh32-v1'
    result = read(base/'RESULT.json')
    for name in ['RESULT.json', 'BUILD.json', 'reproduce.executed.py',
                 'COMPLETE_READBACK_V2.json', 'INDEPENDENT_READBACK.json',
                 'source/HighApplicationAudit.lean']:
        copy(base/name, 'application32/'+name, 'actual fresh32 source/model evidence; pi value symbolic')
    for row in result['build']:
        for suffix in ['stdout', 'stderr', 'resources']:
            relative = 'logs/'+row['module']+'.'+suffix
            copy(base/relative, 'application32/'+relative, 'actual application kernel log', row[suffix+'_sha256'])
    for row in result['dependencies']:
        for suffix in ['stdout', 'stderr']:
            relative = 'dependencies/'+row['module']+'.'+suffix
            copy(base/relative, 'application32/'+relative, 'actual application dependency probe', row[suffix+'_sha256'])
    base = DATA/'high-driver-complete-readback-controls-v3'
    copy(base/'RESULT.json', 'application-reader60/RESULT.json', 'actual60 reader controls, no new theorem')
    for row in read(base/'RESULT.json')['cases']:
        mode = [[], ['-O'], ['-OO']].index(row['flags'])
        for suffix in ['stdout', 'stderr']:
            label = 'nested-output-mode'+str(mode) if row['case'] == 'nested_output_boundary' \
                else 'mode'+str(mode)+'_'+row['case']
            name = label+'.'+suffix
            copy(base/name, 'application-reader60/'+name, 'actual application control log', row[suffix+'_sha256'])
    base = DATA/'high-driver-native-v2'
    for name in ['RESULT.json', 'RUN.json', 'compiler-version', 'rusage',
                 'compile-stdout', 'compile-stderr', 'stderr']:
        copy(base/name, 'native-observation/'+name, 'actual native observation only; not a numerical proof')


def bounded_smoke_evidence():
    base = DATA/'portable-source-smoke-v1'
    for name in ['RESULT.json', 'PLAN.json', 'PROFILES.json', 'PREPARATION_ENVIRONMENT.json',
                 'reproduce.executed.py', 'regenerate.json', 'regenerate.stdout',
                 'regenerate.stderr', 'regenerate.resources', 'compile_all.json',
                 'compile_all.stdout', 'compile_all.stderr', 'compile_all.resources',
                 'base/SOURCES.json', 'base/PREPARED.json', 'base/proposal/PROPOSAL.json',
                 'replay/PLAN.json', 'replay/RESULT.json', 'replay/SCHEDULE.jsonl',
                 'replay/RESOURCE_SAMPLES.jsonl']:
        copy(base/name, 'smoke60/'+name, 'actual60-module N1000 proof and parameterized high-source model')
    result = read(base/'replay/RESULT.json')
    for row in result['records']:
        module = row['module']
        for suffix in ['stdout', 'stderr', 'rusage']:
            source = Path(row[suffix])
            copy(source, 'smoke60/replay/audit/'+module+'/'+suffix,
                 'actual small-run kernel compiler log', row[suffix+'_sha256'])
        for suffix in ['PROBE.json', 'stdout', 'stderr']:
            relative = 'dependencies/'+module+'/'+suffix
            copy(base/relative, 'smoke60/'+relative, 'actual complete small-run dependency probe')
    base = DATA/'portable-completed-controls-v2'
    result = read(base/'RESULT.json')
    copy(base/'RESULT.json', 'portable-reader51/RESULT.json', 'three actual positives and48 labeled mutation-view negatives')
    copy(base/'test.executed.py', 'portable-reader51/test.executed.py', 'actual executed mutation-control source', result['test_sha256'])
    copied = set()
    for row in result['records']:
        mode = [[], ['-O'], ['-OO']].index(row['optimization'])
        for suffix in ['stdout', 'stderr']:
            name = str(mode)+'-'+row['name']+'.'+suffix
            copy(base/name, 'portable-reader51/'+name, 'actual distinct public-CLI control raw log', row[suffix+'_sha256'])
        if 'fixture_sha256' in row and row['name'] not in copied:
            name = row['name']+'.fixture.json'
            copy(base/name, 'portable-reader51/'+name,
                 'documentary read-only mutation view; not another executed proof', row['fixture_sha256'])
            copied.add(row['name'])


def helper_and_stop_evidence():
    for directory, scope in [
        ('cold-static-controls-v1', '54 actual helper CLI decisions; high cold compilation not run'),
        ('physical-engine-gates-v3', '48 actual resource-helper CLI decisions; no new mathematical theorem')]:
        base = DATA/directory
        copy(base/'RESULT.json', directory+'/RESULT.json', scope)
        for index, row in enumerate(read(base/'RESULT.json')['rows']):
            for suffix in ['stdout', 'stderr']:
                name = str(index)+'.'+suffix
                copy(base/name, directory+'/'+name, scope, row[suffix+'_sha256'])
    for directory, names, scope in [
        ('portable-packet-reader-v1', ['RESULT.json', 'COMMAND.json', 'stdout', 'stderr',
                                      'resources', 'open.trace'],
         'actual relocated source-packet reader, not a second proof compilation'),
        ('portable-source-packet-v1', ['PACKET.json'], 'actual121-file source-only packet creation'),
        ('portable-source-packet-v2', ['PACKET.json'],
         'actual130-file source packet with generic bootstrap and all exact pins'),
        ('portable-packet-reader-v2', ['RESULT.json', 'stdout', 'stderr', 'resources', 'open.trace'],
         'actual relocated130-source packet reader; not another proof compilation'),
        ('portable-relocated-smoke-v1-launch', ['LAUNCH.json', 'MEASURED_FORECAST_SUPPLEMENT.json',
                                              'RESOURCE_DRAIN.json', 'stdout', 'stderr', 'resources'],
         'intentionally resource-drained optional control; no acceptance'),
        ('portable-relocated-smoke-v1', ['replay/STOPPED.json', 'compile_all.json'],
         'SIGUSR1 stop after two modules; no accepted numerical proof'),
        ('portable-completed-controls-v1', ['PROGRESS.json', 'test.executed.py',
                                          '0-integer_unchanged_source_flag.stderr'],
         'superseded test expectation mismatch; checker correctly rejected earlier')]:
        for name in names:
            copy(DATA/directory/name, directory+'/'+name, scope)


def main():
    need(not PUBLIC.exists(), 'fresh public evidence namespace')
    PUBLIC.mkdir()
    sources(); existing_grammar_evidence(); application_evidence()
    bounded_smoke_evidence(); helper_and_stop_evidence()
    readme = PUBLIC/'README.md'
    readme.write_text('''# Completed source/model work and bounded clean workflow

This supplement preserves the actual C counter and high-input main, their formal
execution model and correctness proofs, an independently specified bounded C11
syntax with a general soundness theorem, and the source-indexed modeled-output
consumer. The fresh application32 plus grammar5 campaign passed. The separate
60-module clean workflow proved π(1000)=168 and the original high program's
parameterized source/model statement. It did not prove the fixed high output.
The fixed high numerical closure and its cold695+299+Final source consumer remain
incomplete at this publication checkpoint. Prepared source is labeled separately.

The archive includes the actual36 grammar controls,60 strengthened application
reader controls,51 portable controls, and the independent reviews. The51 comprise
three real public-CLI positive readbacks and48 labeled read-only metadata-view
negatives. The intentionally resource-drained optional second small compilation
has no accepted result. A relocated source packet did successfully check the
existing60-module proof, with a recorded file-open trace; this was not another
proof compilation. Original outcomes and failed/stopped receipts are preserved.

The current source-packet recipe includes130 explicitly enumerated files,
including the generic bootstrap and all nine dependency pins. The earlier121-file
packet and the initial ACTUAL_SMOKE_AND_CONTROLS snapshot are historical evidence;
their packet-helper source hashes are not claims about this later recipe.
Create a fresh packet with portable-source-run/make_source_packet.py --out FRESH.
It contains no application proof objects or generated numerical data.

From the packet's project directory, install the pinned Lean4.34.0-rc2 compiler,
then run Solutions/RHOcticPush.v1/integration/continuation/bootstrap_generic.py
with --compiler ABSOLUTE_LEAN --cpu AVAILABLE_CPU --out FRESH_GENERIC.
Use its GENERIC_CONTEXT.json as --context for the portable-source-run/reproduce.py
command documented in that directory's README. The --smoke route is bounded;
the full route regenerates the unchanged fixed high workload and compiles all
mathematical/source consumers. The full fast high route has not been executed
again by this bounded study. Exact recipes, hashes, commands and resource scopes
are retained; no old application object bank is a clean-reproduction input.

The high C main writes eight raw little-endian bytes. Generic compiler, runtime,
ABI, stdio/OS, hardware and model-applicability contracts remain explicit. Bounded
surface-syntax soundness is distinct from full ISO-C semantic adequacy. Kernel
numerical checking alone is not source-first program verification.
''')
    add(readme, 'current completed-versus-pending status and clean source reproduction guide')
    receipt = dict(schema='RH_COMPLETED_COUNTER_PUBLIC_ALLOWLIST_V1',
        status='REVIEW_CANDIDATE_COMPLETED_SYNTAX_MODEL_AND_BOUNDED_WORKFLOW_ONLY',
        fixed_high_numerical_result_complete=False,
        cold695_and299_plus_final_source_consumer_complete=False,
        accepted=['fresh32 application model; pi value symbolic',
                  'fresh37 application+independent C11 syntax/source-indexed model',
                  'actual N1000 clean-source60 proof and parameterized high-source consumer',
                  '51 portable public-CLI control decisions with explicit fixture scope'],
        prepared_not_completed=['all fixed-high2768 numerical proof closure',
                                'source-cold695+299+Final/source-consumer high completion',
                                'full high fast clean recipe execution'],
        exclusions=['application proof objects/caches', 'full numerical certificate/data banks',
                    'multi-GB generated numerical Lean source', 'private contexts/transcripts/handoffs',
                    'source PDFs', 'in-flight count acceptance claims'],
        compiler_and_platform_trust='Pinned generic compiler/libraries, kernel/runtime/ABI/stdio/OS/hardware '
            'and model applicability remain explicit; bounded syntax is not complete ISO-C adequacy.',
        publication_review_required=True, rows=[ROWS[name] for name in sorted(ROWS)],
        total_bytes=sum(q['bytes'] for q in ROWS.values()), copied_evidence=COPIES)
    (PUBLIC/'PUBLIC_ALLOWLIST_CANDIDATE.json').write_text(json.dumps(receipt, indent=2, allow_nan=False)+'\n')
    print('PUBLIC_ALLOWLIST_CANDIDATE', len(ROWS), receipt['total_bytes'])


if __name__ == '__main__':
    main()
