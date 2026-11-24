#!/usr/bin/env python3
"""Run unchanged11+2+3 source append engines after the registered source-only723 runtime-recovery campaign.

This is an execution receipt coordinator, not a mathematical or PV checker.
The public README also gives each constituent command without this coordinator.
"""
from pathlib import Path
import hashlib, json, os, subprocess, sys, time, datetime

D = Path('/data/ivy-rh-octic-20261123')
PACKET = D/'integration/public739-runtime-source-v2'
BASE = D/'integration/public739-runtime-complete723-v1'
CONTEXT = D/'ramanujan/generic-prereq-context-v2/GENERIC_CONTEXT.json'
OUT = D/'integration/public739-runtime-appends-v1'
BASE_PID, BASE_START = 1549622, '1004832616'


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    temporary = path.with_name('.'+path.name+'.pending')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    os.replace(temporary, path)


def alive():
    try:
        fields = Path('/proc').joinpath(str(BASE_PID), 'stat').read_text().rsplit(')', 1)[1].split()
        return fields[0] != 'Z' and fields[19] == BASE_START
    except FileNotFoundError:
        return False


def main():
    own_sha = sha(__file__)
    need(not OUT.exists(), 'fresh separate append execution namespace')
    manifest = read(PACKET/'SOURCE_PACKET.json')
    need(manifest['total_proof_modules_with_declared_appends'] == 739,
         'exact declared739 source packet')
    source = PACKET/'source'
    files = {row['path']: row for row in manifest['files']}
    need(len(files) == manifest['file_count'], 'unique source packet file paths')
    entries = list(source.rglob('*'))
    need(not any(path.is_symlink() for path in entries), 'no source packet symlinks')
    need({path.relative_to(source).as_posix() for path in entries if path.is_file()} == set(files),
         'complete exact source packet inventory')
    for relative, row in files.items():
        need(sha(source/relative) == row['sha256'], 'source packet bytes:'+relative)
    OUT.mkdir()
    (OUT/'coordinator.executed.py').write_bytes(Path(__file__).read_bytes())
    start = time.monotonic()
    env = os.environ.copy()
    env['IEANTN_GENERIC_CONTEXT'] = str(CONTEXT)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env.pop('LEAN_PATH', None)
    solution = source/'Solutions/RHOcticPush.v1'
    save(OUT/'PLAN.json', {'controller_sha256': own_sha,
        'source_packet_sha256': sha(PACKET/'SOURCE_PACKET.json'),
        'generic_context_sha256': sha(CONTEXT),
        'registered_base_controller': {'PID': BASE_PID, 'start_ticks': BASE_START},
        'base': str(BASE), 'scope': 'Sequential unchanged11+2+3 appends above registered fresh723; '
            'no historical application objects or mathematical premise added; explicit runtime recovery.'})
    stages = []
    try:
        while not (BASE/'RESULT.json').exists():
            need(not (BASE/'FAILURE.json').exists() and alive(),
                 'registered base interrupted or rejected; preserve partial execution')
            save(OUT/'PROGRESS.json', {'state': 'waiting for actual registered clean723 receipt',
                'seconds_including_wait': time.monotonic()-start})
            time.sleep(30)
        base_result = read(BASE/'RESULT.json')
        need(base_result['status'] == 'PASS_COMPLETE_SOURCE_ONLY723_PIPELINE'
             and base_result['primary_used_recovery'] is True,
             'complete same-campaign source-only723 with explicit114-prefix runtime recovery')
        need(base_result['generic_context_sha256'] == sha(CONTEXT), 'same execution generic context')
        original = read(D/'integration/public723-source-v1/SOURCE_PACKET.json')
        need(base_result['source_packet_sha256'] == sha(PACKET/'SOURCE_PACKET.json')
             and original['proof_universe'] == manifest['proof_universe'], 'exact same723 science')
        for label, script, foundation in [
            ('feedback734', solution/'integration/feedback/reproduce.py', BASE/'ram60611'),
            ('box725', solution/'comparisons/reproduce_box_lee.py', BASE/'ram60611'),
            ('nl737', solution/'comparisons/reproduce_nl_parabolic.py', OUT/'feedback734')]:
            available = next(int(line.split()[1])*1024 for line in
                             Path('/proc/meminfo').read_text().splitlines()
                             if line.startswith('MemAvailable:'))
            need(available >= 576*(1 << 30), 'preserve512GiB host plus64GiB single source lane')
            target = OUT/label
            command = [sys.executable, '-B', str(script), '--foundation', str(foundation),
                       '--out', str(target)]
            began = time.monotonic()
            with (OUT/(label+'.stdout')).open('w') as stdout, (OUT/(label+'.stderr')).open('w') as stderr:
                process = subprocess.Popen(command, env=env, stdout=stdout, stderr=stderr)
                save(OUT/'ACTIVE_CHILD.json', {'PID': process.pid,
                    'start_ticks': Path('/proc').joinpath(str(process.pid), 'stat')
                                    .read_text().rsplit(')', 1)[1].split()[19],
                    'command': command, 'source_sha256': sha(script)})
                returncode = process.wait()
            need(returncode == 0 and (target/'RESULT.json').is_file(), 'actual append result:'+label)
            receipt = read(target/'RESULT.json')
            need(receipt['controller_sha256'] == sha(script), 'append source controller binding')
            stages.append({'phase': label, 'command': command, 'RESULT_sha256': sha(target/'RESULT.json'),
                'status': receipt['status'], 'observed_full_phase_seconds': time.monotonic()-began,
                'compiler_resource_scope': {key: receipt[key] for key in receipt
                    if key.startswith(('peak_', 'sampled_', 'observed_process_OOM'))}})
            save(OUT/'STAGES.json', stages)
        need(sha(__file__) == own_sha == sha(OUT/'coordinator.executed.py'), 'unchanged executed coordinator')
        for relative, row in files.items():
            need(sha(source/relative) == row['sha256'], 'immutable source packet after compilation')
        save(OUT/'RESULT.json', {'status': 'PASS_FRESH_ANALYTIC739_SOURCE_IDENTITY_UNION',
            'controller_sha256': own_sha, 'source_packet_sha256': sha(PACKET/'SOURCE_PACKET.json'),
            'base_RESULT_sha256': sha(BASE/'RESULT.json'), 'primary_used_recovery': True,
            'source_identity_manifest_sha256': sha(PACKET/'SOURCE_IDENTITIES_739.json'),
            'generic_context_sha256': sha(CONTEXT), 'stages': stages,
            'seconds_including_wait': time.monotonic()-start,
            'source_first_PV_claim': False, 'official_Comparator_receipt': False,
            'composition': {'base': 723, 'feedback': 11, 'Box_Lee': 2, 'NL': 3},
            'qualification': 'The campaign includes an explicit runtime-stage interruption and114-source recovery. 739 is the union of actual source modules, including audits/glue, '
                'not739 new theorems. Each unchanged engine performs its complete recursive acceptance. '
                'Generic libraries were pinned and installed before this application run; a separate '
                'portable generic bootstrap has an independent execution receipt.'})
    except BaseException as error:
        save(OUT/'FAILURE.json', {'error': repr(error), 'completed_phases': len(stages),
            'seconds_including_wait': time.monotonic()-start,
            'note': 'Preserved actual failure; no automatic OOM attribution or mathematical promotion.'})
        raise


if __name__ == '__main__':
    main()
