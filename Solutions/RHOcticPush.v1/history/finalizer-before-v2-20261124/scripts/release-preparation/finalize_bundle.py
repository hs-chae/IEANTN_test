#!/usr/bin/env python3
"""Execute reviewed archival, 6 MB splitting and extracted artifact checks.

This runs no Lean proof compilation and makes no new mathematical acceptance
claim. The caller supplies an independently reviewed exact bundle specification.
Reports and FINAL_STATUS must already be approved inputs of that specification.
Original packets, accepted runs and downloaded parts are never modified.
"""
import argparse
import hashlib
import math
import os
import re
import shutil
import subprocess
import sys
import time
import zipfile
from pathlib import Path
from common import identity, need, read, relative, save, sha
from split_archive import PART_BYTES, split

PREFIX = Path('Solutions/RHOcticPush.v1')


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    parser.add_argument('--spec', type=Path, required=True)
    parser.add_argument('--builder', type=Path, required=True)
    parser.add_argument('--context', type=Path, required=True)
    parser.add_argument('--finite-smoke', type=Path, required=True)
    parser.add_argument('--ieantn-run', type=Path, required=True)
    parser.add_argument('--native-cc', required=True)
    parser.add_argument('--native-cpu', type=int, required=True)
    parser.add_argument('--katex', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    spec = read(args.spec)
    need(spec['status'] == 'REVIEWED_EXPLICIT_PUBLICATION_BUNDLE_INPUTS', 'independently reviewed exact specification')
    need(not args.out.exists() and args.out.parent.is_dir(), 'fresh final validation output')
    need(re.fullmatch('[0-9a-f]{40}', spec['source_commit']), 'actual published source commit')
    args.out.mkdir()
    started = time.monotonic()
    commands = []
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    def run(label, command):
        before = time.monotonic()
        cp = subprocess.run(command, env=environment, capture_output=True)
        (args.out/(label+'.stdout')).write_bytes(cp.stdout)
        (args.out/(label+'.stderr')).write_bytes(cp.stderr)
        commands.append(dict(label=label, command=command, returncode=cp.returncode,
            seconds=time.monotonic()-before, stdout_sha256=sha(args.out/(label+'.stdout')),
            stderr_sha256=sha(args.out/(label+'.stderr'))))
        need(cp.returncode == 0, 'actual extracted command failed: '+label)
    run('archive', [sys.executable, '-B', str(args.builder), '--spec', str(args.spec),
                    '--out', str(args.out/'archive')])
    archive = args.out/'archive/RH_LIMIT_BREAKTHROUGH_EVIDENCE.zip'
    extracted = args.out/'extracted'
    extracted.mkdir()
    with zipfile.ZipFile(archive) as bundle:
        names = bundle.namelist()
        need(len(names) == len(set(names)), 'unique exact archive members')
        for member in names:
            relative(member)
        bundle.extractall(extracted)
    need((extracted/'README.md').is_file() and (extracted/'reassemble_evidence.py').is_file(),
         'actual release guide and reassembler must be included')
    verifier = extracted/'publication'/PREFIX/'scripts/verify_evidence_bundle.py'
    for i, mode in enumerate([[], ['-O'], ['-OO']]):
        run('inventory-'+str(i), [sys.executable, '-B', *mode, str(verifier), '--root', str(extracted)])
    # This observation compiles/runs the unchanged actual C source. Its value
    # is never substituted for a kernel proof or a source/model refinement.
    compiler = shutil.which(args.native_cc)
    need(compiler is not None, 'supplied native GCC11 compiler is available')
    compiler = Path(compiler).resolve()
    run('native-compiler-version', [str(compiler), '-dumpfullversion'])
    need(re.fullmatch(r'11\.\d+(?:\.\d+)?\s*',
                     (args.out/'native-compiler-version.stdout').read_text()) is not None,
         'supplied native compiler must be GCC11')
    need(args.native_cpu in os.sched_getaffinity(0), 'supplied native CPU is available')
    native_helper = extracted/'publication'/PREFIX/'ramanujan/count-feasibility/high-driver/run_native_high.py'
    native = args.out/'native'
    run('ordinary-native-high-observation', [sys.executable, '-B', str(native_helper),
        '--out', str(native), '--cc', str(compiler), '--cpu', str(args.native_cpu)])
    native_result = read(native/'RESULT.json')
    output = (native/'stdout.bin').read_bytes()
    usage = (native/'rusage').read_text()
    counter_sha = '85326ecb93d86c693d980352ebde59a350eef89b4f367c88b65fa88f58d991dd'
    driver_sha = '011738a2ee9879f25d3b24bf7b134ba20825105872a3e3d26d1a082db72140f7'
    need(native_result['status'] == 'ORDINARY_NATIVE_DRIVER_EXECUTION_NOT_YET_SOURCE_FIRST_PV' and
         native_result['source_first_PV_complete'] is False and
         native_result['numerical_output_is_a_proved_count'] is False and
         native_result['input'] == native_result['fixed_source_input'] == 1490000000000 and
         native_result['emitted_word'] == 55206486339 and
         native_result['counter_sha256'] == counter_sha and native_result['driver_sha256'] == driver_sha and
         type(native_result['compile_exit_code']) is int and native_result['compile_exit_code'] == 0 and
         type(native_result['execution_exit_code']) is int and native_result['execution_exit_code'] == 0 and
         type(native_result['output_bytes']) is int and native_result['output_bytes'] == len(output) == 8 and
         native_result['word_byte_order'] == sys.byteorder and
         int.from_bytes(output, byteorder=sys.byteorder, signed=False) == 55206486339,
         'ordinary native observation of the unchanged fixed source and eight-byte output')
    need(sha(native/'source/verified_quotient_count.c') == counter_sha and
         sha(native/'source/verified_quotient_driver_high.c') == driver_sha and
         native_result['compiler'] == str(compiler) and sha(compiler) == native_result['compiler_sha256'] and
         sha(native/'compiler-version') == native_result['compiler_version_sha256'] and
         sha(native/'driver-high') == native_result['executable_sha256'] and
         sha(native/'stdout.bin') == native_result['output_sha256'] and
         sha(native/'stderr') == native_result['stderr_sha256'] and
         sha(native/'rusage') == native_result['rusage_sha256'],
         'actual native source/compiler/executable/output/resource identities')
    for field in ['compile_seconds', 'execution_seconds']:
        need(type(native_result[field]) in [int, float] and math.isfinite(native_result[field]) and
             native_result[field] > 0, 'actual finite native observation times')
    peak = re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)', usage)
    elapsed = re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)', usage)
    timed = re.findall(r'Command being timed: "([^\n]+)"', usage)
    need(len(peak) == 1 and int(peak[0]) > 0 and len(elapsed) == 1 and
         timed == [' '.join(native_result['execution_command'][4:])] and 'Exit status: 0' in usage,
         'actual GNU native execution command, elapsed time and peak RAM')
    native_observation = dict(native_observation_only=True, mathematical_acceptance=False,
        source_first_PV_established_by_this_observation=False, formal_physical_trace=False,
        helper_sha256=sha(native_helper), RESULT_sha256=sha(native/'RESULT.json'),
        compiler_sha256=native_result['compiler_sha256'], compiler=str(compiler),
        executable_sha256=native_result['executable_sha256'], output_sha256=native_result['output_sha256'],
        emitted_word=native_result['emitted_word'], output_bytes=8,
        compile_seconds=native_result['compile_seconds'], execution_seconds=native_result['execution_seconds'],
        GNU_elapsed=elapsed[0], peak_RSS_KiB=int(peak[0]), rusage_sha256=sha(native/'rusage'),
        source_hashes=[counter_sha, driver_sha],
        scope='Ordinary native source-compilation/output reproduction only. The frozen helper historical labels describe this observation; separate accepted Lean source/model/IEANTN proofs retain their own status and trust boundary.')
    save(args.out/'NATIVE_OBSERVATION.json', native_observation)
    parts = args.out/'download'
    manifest = split(archive, sha(archive), parts)
    rows = manifest['parts']
    reassembler = extracted/'reassemble_evidence.py'
    for i, mode in enumerate([[], ['-O'], ['-OO']]):
        output = args.out/('reassembled-'+str(i)+'.zip')
        run('reassembly-'+str(i), [sys.executable, '-B', *mode, str(reassembler),
            '--parts', str(parts/'EVIDENCE_PARTS.json'), '--out', str(output)])
        need(identity(output) == identity(archive), 'actual reassembled archive identity')
    run('analytic-preflight', [sys.executable, '-B',
        str(extracted/'analytic/source'/PREFIX/'integration/continuation/finish_clean_single_lane.py'),
        '--check', '--source-packet', str(extracted/'analytic'), '--context', str(args.context),
        '--primary', str(args.out/'unused-primary'), '--out', str(args.out/'unused-analytic')])
    run('finite-smoke-reader', [sys.executable, '-B',
        str(extracted/'finite/project'/PREFIX/'ramanujan/count-feasibility/portable-source-run/reproduce.py'),
        '--check', str(args.finite_smoke)])
    run('accepted-ieantn-append-reader', [sys.executable, '-B',
        str(extracted/'publication'/PREFIX/'ramanujan/count-feasibility/ieantn-consumer/reproduce.py'),
        '--verify', str(args.ieantn_run)])
    status = extracted/'publication'/PREFIX/'reports/FINAL_STATUS.json'
    actual_status = read(status)
    need(actual_status.get('FinalSourceDone') is True and
         actual_status.get('source_snapshot_commit') == spec['source_commit'] and
         actual_status.get('ieantn_consumer', {}).get('accepted') is True,
         'actual completed final status and published source commit')
    run('report-regeneration', [sys.executable, '-B',
        str(extracted/'publication'/PREFIX/'reports/build_reports.py'), '--status', str(status),
        '--katex', str(args.katex), '--out', str(args.out/'regenerated-reports')])
    reports = sorted((extracted/'reports').glob('*.html'))
    need(len(reports) == 3, 'three actual standalone final reports')
    for report in reports:
        need((args.out/'regenerated-reports'/report.name).read_bytes() == report.read_bytes(),
             'exact final report regeneration: '+report.name)
    # All128 generated Lean and3proposal files are compared by the frozen recipe.
    run('proposal-regeneration', [sys.executable, '-B',
        str(extracted/'analytic/source'/PREFIX/'integration/continuation/regenerate_moments.py'),
        '--out', str(args.out/'regenerated-proposals')])
    save(args.out/'RESULT.json', dict(status='PASS_FINAL_ARCHIVE_PARTS_EXTRACTED_FRONTDOORS_AND_REPORT_REGENERATION',
        source_commit=spec['source_commit'], spec_sha256=sha(args.spec), commands=commands,
        native_observation=native_observation,
        archive=identity(archive), parts_manifest_sha256=sha(parts/'EVIDENCE_PARTS.json'),
        part_bytes=PART_BYTES, parts=len(rows), seconds=time.monotonic()-started,
        mathematical_acceptance=False,
        scope='Artifact and extracted-frontdoor checks, ordinary native output reproduction, and readback of the actual accepted four-source IEANTN append and its inherited basis. The native observation is neither a proof nor a formal physical trace; the append check is readback, not a fresh monolithic high computation. Prior actual scientific runs supply mathematical acceptance; no proof compilation is repeated here.'))
    print('PASS actual final archival, extraction, parts and report/proposal regeneration')


if __name__ == '__main__':
    main()
