#!/usr/bin/env python3
"""Exercise actual bootstrap/rebuilder acceptance CLIs under normal/-O/-OO."""
from pathlib import Path
import argparse, copy, json, os, shutil, subprocess, sys

def need(ok, message):
    if not ok:
        raise ValueError(message)

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--bundle', type=Path, required=True)
    p.add_argument('--context', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(); b = a.bundle.resolve(); need(not a.out.exists(), 'fresh controls output required')
    a.out.mkdir(parents=True); ctx = json.loads(a.context.read_text()); results = []
    def cli(mode, label, script, args, positive=False):
        flags = [] if mode == 0 else ['-O'] if mode == 1 else ['-OO']
        cmd = [sys.executable, *flags, str(b / script), *map(str, args)]
        env = os.environ.copy(); env['PYTHONOPTIMIZE'] = str(mode); env['PYTHONDONTWRITEBYTECODE'] = '1'
        run = subprocess.run(cmd, env=env, text=True, capture_output=True)
        row = {'mode': mode, 'case': label, 'command': cmd, 'PYTHONOPTIMIZE': str(mode),
               'returncode': run.returncode, 'expected_success': positive,
               'stdout': run.stdout, 'stderr': run.stderr}
        results.append(row); (a.out / 'PARTIAL.json').write_text(json.dumps(results, indent=2) + '\n')
        need((run.returncode == 0) == positive, 'unexpected actual CLI result: ' + label)
    for mode in [0, 1, 2]:
        o = a.out / ('mode-' + str(mode)); o.mkdir()
        packages = Path(ctx['generic_dependencies'][0]['path']).parent
        cli(mode, 'positive-bootstrap-input-check', 'BOOTSTRAP_GENERIC.py',
            ['--packages', packages, '--compiler', ctx['compiler'], '--out', o / 'bootstrap-check', '--check'], True)
        cli(mode, 'positive-rebuilder-full-generic-input-check', 'REPRODUCE_BUNDLE.py',
            ['--context', a.context.resolve(), '--out', o / 'rebuilder-check', '--check'], True)
        bad = copy.deepcopy(ctx); bad['compiler_sha256'] = '0' * 64
        badctx = o / 'wrong-compiler-context.json'; badctx.write_text(json.dumps(bad))
        for action in ['capture', 'restore']:
            args = [action, '--bundle', b, '--context', badctx, '--out', o / ('bad-' + action)]
            if action == 'restore':
                args += ['--transport', b / 'generic-transport']
            cli(mode, 'reject-generic-' + action + '-wrong-compiler', 'generic_transport.py', args)
        cli(mode, 'reject-bootstrap-wrong-compiler', 'BOOTSTRAP_GENERIC.py',
            ['--packages', packages, '--compiler', '/bin/true', '--out', o / 'bad-bootstrap', '--check'])
        cli(mode, 'reject-rebuilder-wrong-compiler', 'REPRODUCE_BUNDLE.py',
            ['--context', badctx, '--out', o / 'bad-rebuilder', '--check'])
        duplicate = o / 'duplicate.json'; duplicate.write_text('{"schema":"x","schema":"y"}')
        cli(mode, 'reject-downloader-duplicate-JSON', 'fetch_generic_cache.py',
            ['--manifest', duplicate, '--out', o / 'bad-download', '--check'])
        corrupted = o / 'corrupted-transport'; shutil.copytree(b / 'generic-transport', corrupted)
        with (corrupted / 'GENERIC_BUILD_METADATA.tar.gz').open('ab') as stream:
            stream.write(b'corruption')
        cli(mode, 'reject-corrupted-metadata-archive', 'generic_transport.py',
            ['restore', '--bundle', b, '--context', a.context.resolve(), '--transport', corrupted, '--out', o / 'bad-view'])
        recipe = o / 'corrupted-recipe'; shutil.copytree(b / 'generic-source-recipe', recipe)
        manifest = json.loads((recipe / 'RECIPE.json').read_text()); target = recipe / manifest['modules'][0]['source']
        with target.open('a') as stream:
            stream.write('\n-- corrupted owned negative fixture\n')
        cli(mode, 'reject-corrupted-generic-source', 'bootstrap_missing_generic.py',
            ['--recipe', recipe, '--fresh-bank', o / 'bank-must-not-be-used', '--compiler', ctx['compiler'], '--out', o / 'bad-source-build'])
        cli(mode, 'reject-zero-resource-limit', 'run_bounded.py',
            ['--record', o / 'bad-resource', '--limit-gib', '0', '--', '/bin/true'])
        for script in ['BOOTSTRAP_GENERIC.py', 'REPRODUCE_BUNDLE.py', 'generic_transport.py',
                       'bootstrap_missing_generic.py', 'fetch_generic_cache.py', 'run_bounded.py']:
            cli(mode, 'reject-missing-args-' + script, script, [])
            cli(mode, 'reject-unknown-option-' + script, script, ['--unexpected'])
    result = {'schema': 'GENERIC_BOOTSTRAP_REBUILDER_ACTUAL_ACCEPTANCE_CONTROLS_V1',
              'status': 'PASS_ALL_ACTUAL_CLI_ACCEPTANCE_CONTROLS_NORMAL_O_OO',
              'cases': len(results), 'results': results}
    temp = a.out / 'RESULT.pending'; temp.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(temp, a.out / 'RESULT.json'); print(json.dumps({'status': result['status'], 'cases': len(results)}))

if __name__ == '__main__':
    main()
