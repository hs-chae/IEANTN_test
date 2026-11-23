#!/usr/bin/env python3
"""Draw a deterministic resource figure from frozen, actual replay records.

This plotting-only program reads evidence; it does not run or validate a proof.
No estimated process endpoints, host-memory curve, or performance comparator is
drawn. Completed route spans use literal submitted/accepted schedule events.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.metadata
import json
import math
import os
import platform
import sys

sys.dont_write_bytecode = True
OWNED = Path(__file__).resolve().parent
os.environ.setdefault('MPLCONFIGDIR', str(OWNED / 'matplotlib-config'))
import matplotlib
matplotlib.use('Agg')
from matplotlib import font_manager, pyplot as plt

ROUTES = [('pi', 'π · 261'), ('analytic-absolute', 'Absolute · 114'),
          ('octic', 'Octic · 118'), ('analytic-box', 'Box · 48'),
          ('spectral', 'Spectral · 55'), ('canonical', 'Canonical · 24')]
COLORS = ['#126d92', '#8554a2', '#16836b', '#9d690d', '#b14673', '#4d6078']
FINAL = 'PASS_ALL_RH_LIMIT_FRESH_SOURCE_NUMERICAL_AND_CANONICAL_ROUTES'
HASH_SALT = 'IEANTN_RH_LIMIT_RESOURCE_FIGURE_V1'


def need(value, message):
    if not value:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def decode(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def number(value, label):
    need(type(value) in (int, float) and math.isfinite(value), 'invalid number: ' + label)
    return value


def save(path, value):
    temp = path.with_name(path.name + '.pending')
    need(not temp.exists(), 'preexisting pending metadata')
    temp.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')
    os.replace(temp, path)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--samples', required=True, type=Path)
    parser.add_argument('--orchestrator', required=True, type=Path)
    parser.add_argument('--resources', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--mode', choices=['partial', 'final'], required=True)
    args = parser.parse_args()
    need(args.out.resolve().is_relative_to(OWNED.resolve()) and not args.out.exists(),
         'fresh experiment-owned output directory required')
    paths = {'samples.jsonl': args.samples, 'orchestrator.json': args.orchestrator,
             'resource_state.json': args.resources}
    raw = {name: path.read_bytes() for name, path in paths.items()}
    need(raw['samples.jsonl'].endswith(b'\n'), 'sample snapshot ends inside a record; retry')
    samples = [decode(line) for line in raw['samples.jsonl'].splitlines() if line.strip()]
    state = decode(raw['orchestrator.json'])
    resources = decode(raw['resource_state.json'])
    need(bool(samples), 'no actual samples')
    need(type(resources.get('sample_interval_seconds')) is int
         and resources['sample_interval_seconds'] == 2, 'expected recorded two-second sampling policy')
    previous = -1.0
    for row in samples:
        seconds = number(row['elapsed_seconds'], 'sample elapsed seconds')
        need(seconds >= 0 and seconds > previous, 'samples not strictly ordered')
        need(type(row['tree_RSS_bytes']) is int and row['tree_RSS_bytes'] >= 0,
             'invalid sampled tree RSS')
        previous = seconds
    labels = {name for name, _ in ROUTES}
    submits, finishes = {}, {}
    for event in state.get('schedule_events', []):
        label, kind = event['component'], event['event']
        need(label in labels and kind in ('submitted', 'accepted', 'rejected'), 'unknown schedule event')
        stamp = number(event['monotonic'], 'schedule monotonic time')
        target = submits if kind == 'submitted' else finishes
        need(label not in target, 'duplicate schedule endpoint')
        target[label] = stamp if kind == 'submitted' else (stamp, kind)
    need(bool(submits), 'no observed route submissions')
    for name, (finish, _) in finishes.items():
        need(name in submits and finish >= submits[name], 'completion before submission')
    steps = {}
    for row in state.get('steps', []):
        name = row['component']
        need(name in labels and name not in steps, 'duplicate/unknown completed route')
        steps[name] = row
        if row.get('seconds') is not None:
            need(number(row['seconds'], 'subprocess duration') >= 0, 'negative subprocess duration')
    if args.mode == 'final':
        need(state.get('status') == FINAL, 'full replay has not passed')
        need(resources.get('status') == 'PASS_PROCESS_EXIT_ZERO'
             and type(resources.get('returncode')) is int and resources['returncode'] == 0,
             'resource wrapper has not recorded successful exit')
        need(set(submits) == labels and set(finishes) == labels and set(steps) == labels,
             'not all six routes have actual endpoint records')
        for name in labels:
            row = steps[name]
            need(finishes[name][1] == 'accepted' and row.get('accepted') is True
                 and type(row.get('returncode')) is int and row['returncode'] == 0,
                 'route not accepted: ' + name)
        need(type(resources.get('maximum_sampled_tree_RSS_bytes')) is int
             and resources['maximum_sampled_tree_RSS_bytes'] == max(x['tree_RSS_bytes'] for x in samples),
             'final sampled maximum disagrees with the actual sample stream')
    args.out.mkdir(parents=True)
    frozen = args.out / 'inputs'
    frozen.mkdir()
    for name, content in raw.items():
        (frozen / name).write_bytes(content)

    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10.5,
                         'axes.titlesize': 11.5, 'axes.labelsize': 10,
                         'xtick.labelsize': 9, 'ytick.labelsize': 10,
                         'svg.fonttype': 'path', 'svg.hashsalt': HASH_SALT,
                         'figure.facecolor': 'white', 'axes.facecolor': 'white',
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'axes.edgecolor': '#788391', 'text.color': '#172d40',
                         'axes.labelcolor': '#273b4c', 'xtick.color': '#435465',
                         'ytick.color': '#273b4c'})
    fig, (rss_axis, gantt) = plt.subplots(2, 1, figsize=(6.4, 6.7),
                                         gridspec_kw={'height_ratios': [1.05, 1.2]})
    fig.subplots_adjust(left=.22, right=.95, top=.86, bottom=.23, hspace=.62)
    partial = args.mode == 'partial'
    fig.suptitle('Fresh source replay' + (' — PARTIAL snapshot' if partial else ' — completed'),
                 x=.055, ha='left', y=.975, fontsize=14, fontweight='bold',
                 color='#9b5911' if partial else '#172d40')
    fig.text(.055, .924, 'Frozen candidate: actual resources and recorded schedule', fontsize=10.5)
    times = [x['elapsed_seconds'] / 60 for x in samples]
    memory = [x['tree_RSS_bytes'] / 1024**3 for x in samples]
    maximum = max(memory)
    rss_axis.plot(times, memory, lw=1.1, color='#126d92')
    rss_axis.fill_between(times, memory, 0, color='#126d92', alpha=.11)
    rss_axis.set(xlim=(0, max(times) * 1.01), ylim=(0, maximum * 1.18 if maximum else 1),
                 ylabel='Tree RSS (GiB)', xlabel='Minutes from resource-wrapper start')
    rss_axis.set_title('A  Owned process tree · 2 s sampling', loc='left', pad=9)
    rss_axis.text(.99, .94, 'Largest sample: %.2f GiB' % maximum,
                  transform=rss_axis.transAxes, ha='right', va='top', fontsize=9.5)
    rss_axis.grid(axis='y', color='#dce2e8', lw=.7)
    rss_axis.set_axisbelow(True)

    origin = min(submits.values())
    recorded_endpoints = list(submits.values()) + [x[0] for x in finishes.values()]
    latest = (max(recorded_endpoints) - origin) / 60
    horizon = max(1, latest * 1.06)
    route_rows = []
    for index, ((name, label), color) in enumerate(zip(ROUTES, COLORS)):
        row = {'component': name, 'label': label}
        if name not in submits:
            gantt.text(.015 * horizon, index, 'not submitted', va='center',
                       fontsize=9, color='#79848f', style='italic')
            row['state'] = 'NOT_SUBMITTED'
        else:
            begin = (submits[name] - origin) / 60
            row.update(submitted_monotonic=submits[name], start_minutes_from_first_submission=begin)
            if name not in finishes:
                gantt.scatter([begin], [index], marker='o', s=27, color=color, zorder=3)
                gantt.annotate('submitted; no finish recorded', (begin, index), xytext=(7, 0),
                               textcoords='offset points', va='center', fontsize=8.7, color=color)
                row['state'] = 'SUBMITTED_WITHOUT_RECORDED_FINISH'
            else:
                end, event = finishes[name]
                end_minutes = (end - origin) / 60
                gantt.barh(index, end_minutes - begin, left=begin, height=.58,
                          color=color if event == 'accepted' else '#b03b35', alpha=.9)
                row.update(state=event.upper(), finish_monotonic=end,
                           end_minutes_from_first_submission=end_minutes,
                           recorded_schedule_span_seconds=end - submits[name],
                           measured_subprocess_seconds=steps.get(name, {}).get('seconds'))
        route_rows.append(row)
    gantt.set_yticks(list(range(len(ROUTES))), [label for _, label in ROUTES])
    gantt.set_ylim(len(ROUTES) - .4, -.6)
    gantt.set(xlim=(0, horizon), xlabel='Minutes from first route submission')
    gantt.set_title('B  Submission → accepted receipt', loc='left', pad=10)
    gantt.grid(axis='x', color='#e2e7eb', lw=.7)
    gantt.set_axisbelow(True)
    gantt.tick_params(axis='y', length=0, pad=7)
    gantt.spines['left'].set_visible(False)
    fig.text(.055, .095, 'Sampled RSS is not a continuous peak; summed RSS can count shared pages twice.',
             fontsize=8.2, color='#526171')
    fig.text(.055, .062, 'Route spans include receipt validation. The two clocks retain their recorded origins.',
             fontsize=8.2, color='#526171')
    fig.text(.055, .029, 'No host-total memory, projected endpoints, or comparative speed claim.',
             fontsize=8.2, color='#526171')
    svg = args.out / 'resource-replay.svg'
    png = args.out / 'resource-replay.png'
    fig.savefig(svg, format='svg', metadata={'Date': None,
                'Creator': 'IEANTN deterministic Matplotlib resource figure',
                'Title': 'Actual fresh-source replay resources and schedule' + (' (PARTIAL)' if partial else '')})
    fig.savefig(png, dpi=170, metadata={'Software': 'IEANTN deterministic resource figure'})
    plt.close(fig)
    font = Path(font_manager.findfont('DejaVu Sans'))
    font_files = {style: Path(font_manager.findfont(font_manager.FontProperties(
        family='DejaVu Sans', weight='bold' if style == 'bold' else 'normal',
        style='italic' if style == 'italic' else 'normal')))
                  for style in ['regular', 'bold', 'italic']}
    receipt = {'schema': 'RH_LIMIT_RESOURCE_FIGURE_V1',
               'status': 'PARTIAL_PREVIEW_NOT_FINAL_REPLAY_ACCEPTANCE' if partial else 'FINAL_ACTUAL_COMPLETED_REPLAY_FIGURE',
               'plot_is_not_a_proof_or_PV_claim': True,
               'run_scope': 'Frozen candidate full replay only. Later clean-guard and legacy-consumer replays are separate and are not included in this resource trace.',
               'generator_sha256': digest(Path(__file__).read_bytes()),
               'python_version': platform.python_version(), 'python_executable': sys.executable,
               'matplotlib_version': matplotlib.__version__,
               'package_versions': {x: importlib.metadata.version(x) for x in
                                    ['matplotlib', 'numpy', 'contourpy', 'cycler', 'fonttools',
                                     'kiwisolver', 'packaging', 'pillow', 'pyparsing', 'python-dateutil', 'tzdata']},
               'font_sha256': digest(font.read_bytes()), 'font_name': font.name,
               'font_files': {style: {'name': path.name, 'sha256': digest(path.read_bytes())}
                              for style, path in font_files.items()},
               'svg_hash_salt': HASH_SALT, 'svg_Date_metadata': None,
               'input_sources': {name: str(path) for name, path in paths.items()},
               'input_sha256': {name: digest(content) for name, content in raw.items()},
               'source_orchestrator_status': state.get('status'),
               'source_resource_wrapper_status': resources.get('status'),
               'sample_count': len(samples), 'sampling_interval_seconds': 2,
               'first_sample_elapsed_seconds': samples[0]['elapsed_seconds'],
               'last_sample_elapsed_seconds': samples[-1]['elapsed_seconds'],
               'maximum_observed_sample_RSS_bytes': max(x['tree_RSS_bytes'] for x in samples),
               'actual_OOM_events_as_recorded': resources.get('actual_OOM_events'),
               'OOM_caveat': resources.get('OOM_evidence'),
               'clock_policy': 'RSS uses recorded resource-wrapper elapsed seconds. Route times subtract only the earliest recorded submitted event from literal monotonic events; no cross-clock offset or exact process endpoint is inferred.',
               'route_rows': route_rows,
               'output_sha256': {'resource-replay.svg': digest(svg.read_bytes()),
                                 'resource-replay.png': digest(png.read_bytes())}}
    save(args.out / 'RESULT.json', receipt)
    print(json.dumps({'status': receipt['status'], 'sample_count': len(samples),
                      'svg_sha256': receipt['output_sha256']['resource-replay.svg'],
                      'out': str(args.out)}))


if __name__ == '__main__':
    main()
