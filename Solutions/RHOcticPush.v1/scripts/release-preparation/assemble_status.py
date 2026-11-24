#!/usr/bin/env python3
"""Synthesize actual release gates, never compile or invent missing evidence.

This is a report-status assembler, not a replacement for scientific validators.
Each gate needs an independently supplied exact receipt SHA in the input config.
Missing files/pins are pending; present malformed or changed receipts fail closed.
The default emits a pending snapshot. --final requires every stated gate, an
actual published source commit, and explicit completed theorem/source identities.
"""
import argparse
import copy
import datetime
import re
from pathlib import Path
from common import checked, identity, need, read, relative, save, sha

EXPECTED = {
    'analytic739': 'COMPLETE_ANALYTIC739_CURRENT_CAMPAIGN_WITH_EXPLICIT_RUNTIME_RECOVERY',
    'warm_count': 'COMPLETE_EXACT_COUNT_AND_SOURCE_MODEL_EXECUTION',
    'cold697': 'FRESH_SELECTED_SOURCE_CLOSURE_PASS',
    'cold_data': 'PASS_FRESH695_DATA_AND_GAPS_BYTE_IDENTICAL',
    'remaining305': 'PASS_NO_OLD_APPLICATION_CACHE_COUNT_AND_SOURCE_RUN',
    'cold_controls30': 'PASS_COMPLETED_FULL_COLD695_AND305_PUBLIC_CLI_CONTROLS',
    'ieantn_append4': 'PASS_FRESH_SAME_RUN_SOURCE_BYTES_TO_EXISTING_IEANTN_PI',
    'ieantn_controls24': 'PASS_ALL24_NORMAL_O_OO_ACTUAL_IEANTN_CONSUMER_CONTROLS',
}
WITNESS = 'KERNEL_DERIVED_EXISTING_EXHAUSTIVE_COUNT'


def controls(obj, key, count, field, positive, root):
    records = obj[field]
    need(type(records) is list and len(records) == count, 'exact control population: '+key)
    if key == 'cold_controls30':
        need(obj['decisions'] == count and obj['original_receipt_log_bytes_unchanged'] is True,
             'complete preserved cold control decisions')
        need(all(row.get('passed') is True for row in records), 'all actual cold controls passed')
        names = []
        actual_positive = 0
        for row in records:
            mode = row['optimization']
            need(mode in [[], ['-O'], ['-OO']], 'actual cold optimization mode')
            label = str([[], ['-O'], ['-OO']].index(mode))+'-'+row['name']
            names.append(label)
            stdout = root/(label+'.stdout')
            stderr = root/(label+'.stderr')
            need(sha(stdout) == row['stdout_sha256'] and sha(stderr) == row['stderr_sha256'],
                 'actual distinct cold control log hashes')
            expected = row['expected_gate']
            if expected is None:
                actual_positive += 1
                need(row['returncode'] == 0 and 'PASS_' in stdout.read_text(), 'actual positive cold readback')
            else:
                need(type(expected) is str and row['returncode'] != 0 and expected in stderr.read_text(),
                     'specific actual cold mutation rejection')
        need(len(set(names)) == count and actual_positive == positive, 'distinct matched actual cold cases')
    else:
        need(obj['positive'] == positive and obj['rehashed_source_rejections'] == 3 and
             obj['rehashed_output_rejections'] == 3 and obj['false_exact_target_rejections'] == 3 and
             obj['wrong_timed_argv_rejections'] == 3 and obj['owned_context_log_dependency_rejections'] == 9 and
             obj['accepted_run_unchanged'] is True, 'complete preserved IEANTN control decisions')
        kinds = ['positive', 'rehashed_source', 'rehashed_output', 'false_exact_target',
                 'wrong_timed_argv', 'symlink_context', 'symlink_log', 'symlink_dependency']
        labels = {mode+'-'+kind for mode in ['normal', 'O', 'OO'] for kind in kinds}
        need(count == 24 and {row['case'] for row in records} == labels,
             'exact24 IEANTN control labels and classes')
        expected_gates = {
            'positive': None,
            'rehashed_source': 'frozen append source:WordBytesBounded',
            'rehashed_output': 'one actual IEANTN VALUE payload',
            'false_exact_target': 'complete exact same-run/grammar/correctness/byte VALUE audit',
            'wrong_timed_argv': 'actual GNU timed compiler argv',
            'symlink_context': 'owned regular nonsymlink artifact:GENERIC_CONTEXT.executed.json',
            'symlink_log': 'owned regular nonsymlink artifact:logs/WordBytesBounded.stdout',
            'symlink_dependency': 'owned regular nonsymlink artifact:dependencies/WordBytesBounded.stdout',
        }
        expanded = []
        need(len({row['case'] for row in records}) == count, 'distinct actual control cases')
        for row in records:
            path = root/relative(row['receipt'])
            need(sha(path) == row['receipt_sha256'], 'nested actual control receipt identity')
            item = read(path)
            need(item['case'] == row['case'], 'nested actual control case association')
            mode = row['case'].split('-', 1)[0]
            flags = [flag for flag in item['command'] if flag in ['-O', '-OO']]
            need(flags == {'normal': [], 'O': ['-O'], 'OO': ['-OO']}[mode] and
                 item['command'].count('--verify') == 1,
                 'actual control command matches its exact mode and readback route')
            for suffix in ['stdout', 'stderr']:
                need(sha(path.parent/(suffix+'.txt')) == item[suffix+'_sha256'], 'actual control log bytes')
            expected = item['expected_rejection']
            kind = row['case'].split('-', 1)[1]
            need(expected == expected_gates[kind], 'exact specific IEANTN control rejection class')
            stdout = (path.parent/'stdout.txt').read_text()
            stderr = (path.parent/'stderr.txt').read_text()
            need((expected is None and item['returncode'] == 0 and
                  'PASS_IEANTN_SAME_RUN_BYTE_CONSUMER_READBACK' in stdout) or
                 (type(expected) is str and item['returncode'] != 0 and expected in stderr and
                  'PASS_IEANTN_SAME_RUN_BYTE_CONSUMER_READBACK' not in stdout),
                 'specific actual consumer control decision')
            expanded.append(item)
        records = expanded
    # Check actual command/log evidence and distinguish normal/-O/-OO outputs.
    for row in records:
        need(type(row['command']) is list and row['command'], 'actual control command')
        need(type(row['returncode']) is int, 'actual integer control return code')
        for suffix in ['stdout', 'stderr']:
            need(re.fullmatch('[0-9a-f]{64}', row[suffix+'_sha256']), 'actual control log hash')
    modes = [tuple(flag for flag in row['command'] if flag in ['-O', '-OO']) for row in records]
    need(set(modes) == {(), ('-O',), ('-OO',)} and
         all(modes.count(mode) == count//3 for mode in set(modes)), 'matched optimization modes')


def source_identity(root, row, allow_module_command=False):
    fields = {'file', 'declaration', 'physical_line', 'sha256'}
    module_command = row.get('kind') == 'module_command'
    if module_command:
        need(allow_module_command is True and set(row) == fields | {'kind'} and
             row['file'] == 'Solutions/RHOcticPush.v1/ramanujan/count-feasibility/final-completion-v1/source/CountSourceAudit.lean' and
             row['declaration'] == 'run_cmd', 'exact allowed captured audit module-command identity')
    else:
        need(set(row) == fields, 'exact written source identity')
    path = root/row['file']
    need(identity(path)['sha256'] == row['sha256'] and type(row['physical_line']) is int
         and row['physical_line'] > 0, 'current exact theorem bytes and declaration line')
    lines = path.read_bytes().decode('utf-8').split('\n')
    need(row['physical_line'] <= len(lines), 'actual physical LF source locator')
    line = lines[row['physical_line']-1]
    if module_command:
        need(re.match(r'^run_cmd do(?:\s|$)', line) is not None,
             'actual captured audit module-command physical LF locator')
    else:
        short = row['declaration'].split('.')[-1]
        need(re.search(r'\b(?:theorem|lemma|def)\s+'+re.escape(short)+r'\b', line),
             'actual written theorem declaration locator')
    return row


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    parser.add_argument('--base', type=Path, required=True)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--source-commit')
    parser.add_argument('--final', action='store_true')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    need(not args.out.exists(), 'fresh status output directory')
    config, base = read(args.config), read(args.base)
    need(set(config['gates']) == set(EXPECTED), 'all eight actual acceptance gates required')
    accepted, receipts, values = {}, {}, {}
    for key, wanted in EXPECTED.items():
        item = config['gates'][key]
        path = Path(item['path'])
        if not path.is_file() or item.get('sha256') is None:
            accepted[key] = False
            receipts[key] = dict(accepted=False,
                reason='receipt missing' if not path.is_file() else 'independent final SHA pin pending')
            continue
        need(re.fullmatch('[0-9a-f]{64}', item['sha256']) and sha(path) == item['sha256'],
             'actual pinned result differs: '+key)
        value = read(path)
        need(value['status'] == wanted, 'actual acceptance status differs: '+key)
        accepted[key], values[key] = True, value
        receipts[key] = dict(accepted=True, sha256=sha(path), status=wanted, bytes=path.stat().st_size)
    if accepted['analytic739']:
        need(values['analytic739']['source_modules'] == 739 and
             values['analytic739']['alloriginalLeanmathematicalsourcehashesunchanged'] is True,
             'exact unchanged739 analytic source union')
    if accepted['warm_count']:
        obj = values['warm_count']
        manifest = Path(config['gates']['warm_count']['path']).parent/'MANIFEST.json'
        need(obj['actual_count'] == [1490000000000, 55206486339] and
             sha(manifest) == obj['manifest_sha256'] and
             read(manifest)['mathematical_target'] == obj['actual_count'] and
             any(row['module'] == 'RamanujanPV.HighTransitionCount.Final' for row in obj['records']),
             'locked exact count and unchanged complete Final; prior arithmetic evidence remains in origin provenance')
    if accepted['cold697']:
        need(len(values['cold697']['records']) == 697 and values['cold697']['oom_events'] == 0,
             'actual source697 kernel records')
    if accepted['cold_data']:
        need(values['cold_data']['exact_source_fresh_modules'] == 695 and
             values['cold_data']['no_historical_application_objects'] is True,
             '695 scientific data modules and no old application cache')
        if accepted['cold697']:
            need(values['cold_data']['replay_result_sha256'] == receipts['cold697']['sha256'],
                 'cold scientific/compiler receipt association')
    if accepted['remaining305']:
        need(len(values['remaining305']['records']) == 305 and
             values['remaining305']['no_historical_application_objects'] is True,
             'actual complete305 source-built proof records')
    if accepted['cold_controls30']:
        obj = values['cold_controls30']
        controls(obj, 'cold_controls30', 30, 'records', 6,
                 Path(config['gates']['cold_controls30']['path']).parent)
        need(accepted['cold_data'] and accepted['remaining305'] and
             obj['data_result_sha256'] == receipts['cold_data']['sha256'] and
             obj['remaining_result_sha256'] == receipts['remaining305']['sha256'],
             'cold control results bound to actual accepted proofs')
    if accepted['ieantn_append4']:
        obj = values['ieantn_append4']
        need(len(obj['compilations']) == 4 and accepted['remaining305'] and
             obj['basis']['RESULT_sha256'] == receipts['remaining305']['sha256'] and
             obj['DEV_objects_used'] is False and obj['new_native_verification'] is False,
             'new four-source actual IEANTN consumer and accepted305 basis')
    if accepted['ieantn_controls24']:
        obj = values['ieantn_controls24']
        controls(obj, 'ieantn_controls24', 24, 'cases', 3,
                 Path(config['gates']['ieantn_controls24']['path']).parent)
        need(accepted['ieantn_append4'] and
             obj['actual_RESULT_sha256'] == receipts['ieantn_append4']['sha256'] and
             obj['checker_sha256'] == values['ieantn_append4']['controller_sha256'],
             'consumer control proof result association')
    all_done = all(accepted.values())
    if args.final:
        need(all_done, 'final release still has pending actual gates')
        need(type(args.source_commit) is str and re.fullmatch('[0-9a-f]{40}', args.source_commit),
             'actual reviewed published source commit required for final status')
    if args.source_commit:
        need(re.fullmatch('[0-9a-f]{40}', args.source_commit), 'exact source commit')
    publication_rows = None
    if args.final:
        item = config.get('source_publication')
        need(type(item) is dict and set(item) == {'path', 'sha256'},
             'actual independent source-publication receipt required')
        path = Path(item['path'])
        need(sha(path) == item['sha256'], 'actual source-publication receipt identity')
        published = read(path)
        need(published['commit'] == args.source_commit and
             type(published['status']) is str and published['status'].startswith('PASS_') and
             type(published['rows']) is list, 'actual successful remote source readback for this commit')
        publication_rows = {}
        for row in published['rows']:
            need(row['path'] not in publication_rows, 'unique published source identity')
            publication_rows[row['path']] = row
    status = copy.deepcopy(base)
    status['status'] = 'REVIEWED_RESEARCH_RESULTS' if args.final else 'DRAFT_RESEARCH_IN_PROGRESS'
    status['release_preparation_status'] = ('COMPLETED_ACTUAL_GATES_AWAITING_FINAL_ARTIFACT_REVIEW' if args.final else
                                            'PENDING_RELEASE_GATE_SNAPSHOT_NOT_FINAL')
    status['snapshot_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    if args.source_commit:
        status['source_snapshot_commit'] = args.source_commit
    status['complete_new_source_replay_accepted'] = accepted['analytic739']
    if accepted['analytic739']:
        analytic = values['analytic739']
        status['primary_new_replay_status'] = 'COMPLETE_ANALYTIC739_CURRENT_CAMPAIGN_WITH_EXPLICIT_RUNTIME_RECOVERY'
        current = status.setdefault('independent_compact_reproduction', {})
        current.update(status='Accepted complete739-source identity union and actual independent final readback; original fresh454 runtime omission and strict114-source same-campaign recovery preserved.',
            uninterrupted_from_new_packet_success=False, current_739_final_accepted=True,
            base723_RESULT_sha256=analytic['base723_RESULT_sha256'],
            final739_RESULT_sha256=analytic['final739_RESULT_sha256'],
            independent739_audit_sha256=analytic['independent739_audit_sha256'])
        status['clean_reproduction_summary_en'] = ('The analytic source-only campaign completed the exact739-module union and independent final source/object/compiler/dependency readback. An original fresh454-source attempt failed at a missing C runtime harness; the corrected immutable packet reran the native workloads and strictly reused114 source-built modules from that same campaign. The other625 modules were freshly compiled in this campaign. This is an explicitly resumed source-only reproduction, with the original failure and all provenance preserved.')
        status['clean_reproduction_summary_ko'] = ('해석 소스 전용 재현에서 정확히739개 모듈의 합집합과 최종 소스·객체·컴파일러·의존성의 독립 재검사를 완료했다. 처음454개 소스를 새로 컴파일한 실행은 C 실행 스크립트 누락으로 실패했다. 수정한 불변 패킷에서 실제 네이티브 계산을 다시 수행하고 같은 연구에서 소스로 컴파일한114개 모듈만 엄격히 재사용했다. 나머지625개 모듈도 이번 연구에서 새로 컴파일했다. 처음 실패와 모든 출처를 보존한 명시적 복구 재현이며 중단 없는 실행이라고 주장하지 않는다.')
    status['release_gate_receipts'] = receipts
    status['release_resource_records'] = {}
    for key, obj in values.items():
        resources = {name: obj[name] for name in
            ['seconds', 'seconds_this_attempt', 'resource_peaks', 'resource_peaks_this_attempt',
             'owned_scratch_final_bytes', 'actual_peak_worker_rss_bytes', 'oom_events'] if name in obj}
        if resources:
            status['release_resource_records'][key] = dict(
                RESULT_sha256=receipts[key]['sha256'], recorded_fields=resources,
                scope='Original receipt field names and execution scope; overlapping stages are not summed.')
    status['finite_count_snapshot']['final_accepted'] = accepted['warm_count']
    if all_done:
        status['finite_count_snapshot']['observed_live_workers'] = 0
        status['finite_count_snapshot']['snapshot_utc'] = status['snapshot_utc']
    else:
        status['finite_count_snapshot']['observation_scope'] = ('Preserved dated base-status observation, not a current live-worker claim. Other source-completion stages may still be running.')
    source_done = all(accepted[key] for key in
        ['warm_count', 'cold697', 'cold_data', 'remaining305', 'cold_controls30'])
    status['finite_source_clean_complement'] = ('Accepted actual source-built697 compiler modules plus305 remaining proof/consumer modules, with matched30 actual CLI controls; original warm arithmetic provenance is retained.'
        if source_done else 'Actual source-completion gates still pending: '+', '.join(
            key for key in ['cold697', 'cold_data', 'remaining305', 'cold_controls30'] if not accepted[key]))
    status['finite_source_completion'] = dict(accepted=source_done,
        status='ACCEPTED_SELECTED_SOURCE_MODEL_COUNT_CHAIN' if source_done else 'PENDING_ACTUAL_SOURCE_COMPLETION_GATES')
    if source_done:
        sources = config.get('captured_sources', [])
        need(len(sources) == 3, 'three actual compiled source/model/count identities required')
        status['finite_source_completion']['captured_sources'] = [source_identity(args.source_root, row, allow_module_command=True) for row in sources]
    consumer_done = source_done and accepted['ieantn_append4'] and accepted['ieantn_controls24']
    status['ieantn_consumer'] = dict(accepted=consumer_done)
    if consumer_done:
        obj = status['ieantn_consumer']
        obj.update(basis305_accepted=True, append_accepted=True, controls_accepted=True,
            basis_RESULT_sha256=receipts['remaining305']['sha256'],
            append_RESULT_sha256=receipts['ieantn_append4']['sha256'],
            controls_RESULT_sha256=receipts['ieantn_controls24']['sha256'], numerical_witness=WITNESS,
            new_native_verification=False, physical_trace_claim=False, whole_ISO_C_adequacy_claim=False,
            canonical_point_node_added=False, full_Ramanujan_finite_coverage=False)
        for key in ['theorem_identity', 'byte_lemma_identity']:
            obj[key] = source_identity(args.source_root, config[key])
        code = config['source_code']
        need(len(code) == 2 and len({row['file'] for row in code}) == 2, 'two actual C sources')
        for row in code:
            need(identity(args.source_root/row['file'])['sha256'] == row['sha256'], 'actual C source bytes')
        obj['source_code'] = code
    status['FinalSourceDone'] = consumer_done
    status['remaining'] = [key for key in EXPECTED if not accepted[key]]
    status['artifact_release_followup'] = dict(snapshot_utc=status['snapshot_utc'],
        note='Final report/browser/source-fidelity review, evidence-bundle checks, reviewed publication and attachment delivery occur after rendering; see their separate final release receipts. This note is not a claim that those actions have finished.')
    status['execution_reproduction_scope'] = dict(
        actual_high_result_route='Preserved current-campaign warm exact arithmetic provenance plus actual fresh cold697 and305 complement, followed by the actual separate four-source IEANTN append and controls when accepted.',
        monolithic_clean_full_high_recipe='Prepared deterministic standalone source-only regeneration recipe; the bounded smoke was actually executed separately. This status does not claim that a monolithic full-high portable run was executed.',
        portable_IEANTN_append_recipe='Separate supported clean-basis adapter/documentation must identify its exact checked scope. The actual incremental append acceptance is not evidence that every clean portable procedure was executed.')
    official = status.get('official_Comparator')
    if not (type(official) is dict and official.get('accepted') is True):
        status['remaining'].append('Official IEANTN Comparator workflow receipt remains separate and is not impersonated by local source/kernel audits.')
    if args.final:
        required = list(status['finite_source_completion']['captured_sources'])
        required += [status['ieantn_consumer'][key] for key in ['theorem_identity', 'byte_lemma_identity']]
        required += status['ieantn_consumer']['source_code']
        for row in required:
            need(row['file'] in publication_rows and
                 publication_rows[row['file']]['sha256'] == row['sha256'],
                 'actual theorem/source bytes must be present in independently read-back source commit: '+row['file'])
        status['source_publication_receipt_sha256'] = config['source_publication']['sha256']
    args.out.mkdir()
    save(args.out/('FINAL_STATUS.json' if args.final else 'PENDING_STATUS.json'), status)
    save(args.out/'RESULT.json', dict(status='PASS_ACTUAL_RECEIPT_STATUS_SYNTHESIS', final_requested=args.final,
        all_actual_gates=all_done, gates=accepted, pending=[key for key in accepted if not accepted[key]],
        base_sha256=sha(args.base), config_sha256=sha(args.config),
        scope='Status synthesis from pinned receipts; original validators and independent report review remain required.'))
    print('PASS actual gate snapshot; complete:', all_done, 'pending:', ', '.join(key for key in accepted if not accepted[key]))


if __name__ == '__main__':
    main()
