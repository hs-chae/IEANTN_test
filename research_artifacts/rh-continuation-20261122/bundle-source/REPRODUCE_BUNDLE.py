#!/usr/bin/env python3
"""Replay the archived source tree with only externally supplied pinned generic libraries."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, time
sys.dont_write_bytecode = True
from prepare_bundle import need, strict, verify, save

def main():
    here = Path(__file__).resolve().parent
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--packages', type=Path)
    p.add_argument('--compiler', type=Path)
    p.add_argument('--context', type=Path)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--component', choices=['all', 'integration', 'clog', 'ramanujan', 'ramanujan-nodes', 'signed', 'mobius', 'signed-nodes'], default='all')
    p.add_argument('--strong-run', type=Path)
    p.add_argument('--signed-run', type=Path)
    p.add_argument('--mobius-run', type=Path)
    p.add_argument('--check', action='store_true')
    a = p.parse_args(); out = a.out.resolve()
    need((a.context is not None and a.packages is None and a.compiler is None) or
         (a.context is None and a.packages is not None and a.compiler is not None),
         'supply --context OR both --packages and --compiler')
    need((a.component == 'ramanujan-nodes') == (a.strong_run is not None),
         '--strong-run is required only for explicit --component ramanujan-nodes')
    need((a.component == 'signed-nodes') == (a.signed_run is not None and a.mobius_run is not None),
         '--signed-run and --mobius-run are required only for explicit --component signed-nodes')
    need(a.component == 'signed-nodes' or (a.signed_run is None and a.mobius_run is None),
         'unexpected supplied signed/Mobius banks')
    need(not out.exists() and not out.is_relative_to(here), 'fresh scratch output outside bundle required')
    need(sys.version_info >= (3, 11), 'Python 3.11 or newer required')
    for command in ['git', 'cc']:
        need(shutil.which(command), 'missing prerequisite: ' + command)
    need(Path('/usr/bin/time').is_file(), 'GNU /usr/bin/time required')
    count = verify(here); out.mkdir(parents=True)
    source = here / 'network/Solutions/RHContinuation.v1'
    planned = (['integration', 'clog', 'ramanujan', 'ramanujan-nodes', 'signed', 'mobius', 'signed-nodes']
        if a.component == 'all' else ['ramanujan', 'ramanujan-nodes']
        if a.component == 'ramanujan' else [a.component])
    source_scripts = {'integration': source / 'integration/reproduce_public.py',
        'clog': source / 'parabolic/reproduce_clog.py', 'ramanujan': source / 'ramanujan/reproduce_strong.py',
        'ramanujan-nodes': source / 'ramanujan/node_publication/reproduce.py',
        'signed': source / 'signed/reproduce.py', 'mobius': source / 'signed/mobius/reproduce.py',
        'signed-nodes': here / 'reproduce_signed_nodes.py'}
    for name in planned:
        need(source_scripts[name].is_file(), 'missing active scientific child route: ' + name)
    context = out / 'generic-context.json'
    if a.context is None:
        command = [sys.executable, str(source / 'ramanujan/configure_context.py'),
                   '--packages', str(a.packages.resolve()), '--compiler', str(a.compiler.resolve()),
                   '--out', str(context)]
        configured = subprocess.run(command, text=True, capture_output=True)
        (out / 'configure.stdout').write_text(configured.stdout)
        (out / 'configure.stderr').write_text(configured.stderr)
        need(configured.returncode == 0, 'exact generic context configuration failed')
    else:
        from generic_transport import checked_context
        ctx = checked_context(here, a.context.resolve()); save(context, ctx)
        # A context supplied by the fresh generic bootstrap passes the actual,
        # unchanged legacy full-file gate before any scientific component runs.
        old = here / 'network/Solutions/RHExposureStudy.v1/Ramanujan640/REPRODUCE.py'
        command = [sys.executable, str(old), '--check', '--compiler', ctx['compiler']]
        for row in strict(old.parent / 'SOURCE_MANIFEST.json')['generic_libraries']:
            selected = [r for r in ctx['generic_dependencies'] if r['name'] == row['name']]
            need(len(selected) == 1, 'exact legacy generic association')
            command += ['--generic-root', row['name'] + '=' + selected[0]['library']]
        gated = subprocess.run(command, text=True, capture_output=True)
        (out / 'generic-full-gate.stdout').write_text(gated.stdout)
        (out / 'generic-full-gate.stderr').write_text(gated.stderr)
        need(gated.returncode == 0, 'unchanged legacy generic inventory gate failed')
    env = os.environ.copy(); env['IEANTN_GENERIC_CONTEXT'] = str(context)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    # Component controllers choose and audit their own Python modes explicitly.
    # Keep an ambient setting from overriding their normal-mode child routes.
    env.pop('PYTHONOPTIMIZE', None)
    # Remove application search paths. Every active builder replaces LEAN_PATH
    # with its own fresh objects plus the exact generic libraries.
    env.pop('LEAN_PATH', None)
    if a.check:
        checks = [
            [sys.executable, str(source / 'ramanujan/reproduce.py'), '--check'],
            [sys.executable, str(source / 'signed/reproduce.py'), '--context', str(context), '--check'],
            [sys.executable, str(source / 'signed/mobius/reproduce.py'), '--context', str(context), '--check'],
        ]
        for index, cmd in enumerate(checks):
            run = subprocess.run(cmd, env=env, text=True, capture_output=True)
            (out / ('check-' + str(index) + '.stdout')).write_text(run.stdout)
            (out / ('check-' + str(index) + '.stderr')).write_text(run.stderr)
            need(run.returncode == 0, 'source-only preflight failed: ' + str(index))
        save(out / 'RESULT.json', {'status': 'PASS_BUNDLE_LAYOUT_COMPILER_DEPENDENCY_SOURCE_PREFLIGHT_ONLY',
             'bundle_files': count, 'checks': len(checks), 'python_optimization': sys.flags.optimize,
             'full_old146_generic_file_inventory_checked': a.context is not None, 'mathematical_replay_performed': False})
        print('PASS_BUNDLE_SOURCE_PREFLIGHT_ONLY'); return
    components = planned
    routes = {
        'integration': ('integration/reproduce_public.py', 'RESULT.json', 'PASS_COMPLETE_PUBLIC_SOLUTION_SOURCE_REPLAY'),
        'clog': ('parabolic/reproduce_clog.py', 'RESULT.json', 'PASS'),
        'ramanujan': ('ramanujan/reproduce_strong.py', 'RESULT.json', 'PASS_FRESH_SOURCE_LINKED_ACTUAL_ONE_TWELFTH_CONSUMER'),
        'ramanujan-nodes': ('ramanujan/node_publication/reproduce.py', 'RESULT.json', 'PASS_CANONICAL_NODE_TYPED_SOLUTION_AND_ACTUAL_LI_MODEL'),
        'signed': ('signed/reproduce.py', 'REPLAY_RESULT.json', 'PASS_18_MODULE_27_NEW_THEOREM_FULL_SOURCE_REPLAY'),
        'mobius': ('signed/mobius/reproduce.py', 'REPLAY_RESULT.json', 'PASS_7_MODULE_25_KERNEL_COMPONENTS_WITH_EXPLICIT_ANALYTIC_GAPS'),
        'signed-nodes': ('reproduce_signed_nodes.py', 'RESULT.json', 'PASS_THREE_CANONICAL_SIGNED_NODES_SIX_TYPED_OUTPUTS'),
    }
    result = {'schema': 'PUBLIC_BUNDLE_SOURCE_REPLAY_V1', 'status': 'RUNNING',
              'python_optimization': sys.flags.optimize, 'components': [],
              'only_pinned_external_generic_libraries_allowed': True,
              'compiler_context_sha256': hashlib.sha256(context.read_bytes()).hexdigest()}
    save(out / 'RESULT.json', result); started = time.monotonic()
    try:
        for name in components:
            script, receipt_name, expected = routes[name]
            dest = out / name
            script_path = here / script if name == 'signed-nodes' else source / script
            flags = ([] if sys.flags.optimize == 0 else ['-O'] if sys.flags.optimize == 1 else ['-OO']) if name in {'ramanujan-nodes', 'signed-nodes'} else []
            cmd = [sys.executable, *flags, str(script_path), '--out', str(dest)]
            if name in {'signed', 'mobius'}:
                cmd += ['--context', str(context)]
            elif name == 'ramanujan-nodes':
                cmd += ['--strong-run', str(a.strong_run.resolve() if a.strong_run else out / 'ramanujan')]
            elif name == 'signed-nodes':
                cmd += ['--network', str(here / 'network'), '--context', str(context),
                        '--signed-run', str(a.signed_run.resolve() if a.signed_run else out / 'signed'),
                        '--mobius-run', str(a.mobius_run.resolve() if a.mobius_run else out / 'mobius')]
            control = [sys.executable, str(here / 'run_bounded.py'), '--record', str(out / (name + '-resource-record')),
                       '--limit-gib', '80', '--wall-seconds', '10800', '--', *cmd]
            run = subprocess.run(control, env=env, text=True, capture_output=True)
            (out / (name + '.stdout')).write_text(run.stdout)
            (out / (name + '.stderr')).write_text(run.stderr)
            need(run.returncode == 0, 'bounded source replay failed: ' + name)
            receipt = dest / receipt_name; data = strict(receipt)
            need(data['status'] == expected, 'mathematical source replay gate failed: ' + name)
            result['components'].append({'component': name, 'command': cmd, 'status': data['status'],
                'receipt': str(receipt), 'receipt_sha256': hashlib.sha256(receipt.read_bytes()).hexdigest()})
            save(out / 'RESULT.json', result)
        result.update(status='PASS_REQUESTED_BUNDLE_SOURCE_REPLAY_COMPONENTS', elapsed_seconds=time.monotonic() - started,
                      mathematical_scope='Explicit RH/literature/analytic premises and open full-prime-count source-first PV obligations are unchanged; read each source receipt and the reports.')
        save(out / 'RESULT.json', result); print(result['status'])
    except BaseException as error:
        result.update(status='FAILED_OR_PARTIAL_BUNDLE_REPLAY', error=str(error), elapsed_seconds=time.monotonic() - started)
        save(out / 'RESULT.json', result); raise

if __name__ == '__main__':
    main()
