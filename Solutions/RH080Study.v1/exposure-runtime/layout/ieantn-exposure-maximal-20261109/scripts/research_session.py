"""Fresh model sessions over the existing credential-isolated namespace executor.

The trusted controller has model authentication. Discovery processes receive
only their arm packet and identical pinned generic development tools.
"""
from pathlib import Path
import argparse
import asyncio
import datetime
import hashlib
import json
import os
import resource
import shutil
import signal
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'sources/controller/continuation-20261108'
sys.path.insert(0, str(VENDOR / 'research'))
from existing_executor_adapter import ExistingExecutorAdapter
sys.path.insert(0, str(ROOT / 'scripts'))
import native_session_core as CORE


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strict_load(path):
    def pairs(rows):
        value = {}
        for key, item in rows:
            need(key not in value, 'duplicate JSON key')
            value[key] = item
        return value
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def make_prompt(packet):
    task = packet / 'TASK.md' if (packet / 'TASK.md').is_file() else packet / 'task.md'
    text = task.read_text()
    for path in sorted(packet.rglob('*')):
        need(not path.is_symlink(), 'packet symlink forbidden')
        if not path.is_file() or path.name in {task.name, 'VISIBLE_MANIFEST.json', 'MANIFEST.json'}:
            continue
        raw = path.read_bytes()
        try:
            body = raw.decode('utf-8')
        except UnicodeError:
            body = None
        if body is None or len(raw) > 80_000:
            body = ('Complete file available in the offline filesystem. Bytes=' + str(len(raw))
                    + '; SHA256=' + hashlib.sha256(raw).hexdigest())
        text += ('\n\n===== EXACT FILE /task/' + str(path.relative_to(packet)) + ' =====\n'
                 + body + '\n===== END FILE =====\n')
    return text


class ResearchExecutor(ExistingExecutorAdapter):
    async def start(self):
        self.address_space_limit = ARGS.memory_gib * 1024 ** 3
        self.cpu_limit = ARGS.wall
        self.file_size_limit = 64 * 1024 ** 2
        url = await super().start()
        spec = strict_load(self.spec_path)
        spec.update(tmpfsSize='8g', tmpSize='512m', network='offline')
        # Only generic packages, never an old IEANTN application object or source.
        if ARGS.compiler:
            environment = strict_load(ARGS.environment)
            need(environment['project_objects_reused'] is False, 'generic environment required')
            spec['entries'].append(dict(kind='ro', path='/opt/lean',
                                        source=environment['toolchain']))
            paths = []
            names = {'batteries': 'Batteries', 'Qq': 'Qq', 'aesop': 'Aesop',
                     'proofwidgets': 'ProofWidgets', 'importGraph': 'ImportGraph',
                     'LeanSearchClient': 'LeanSearchClient', 'plausible': 'Plausible',
                     'mathlib': 'Mathlib'}
            for entry in environment['generic_dependencies']:
                spec['entries'].append(dict(kind='ro', path=entry['target'],
                                            source=entry['objects']))
                paths.append(entry['target'])
                source = Path(entry['source']) / names[entry['name']]
                if source.is_dir():
                    spec['entries'].append(dict(kind='ro',
                        path='/generic-source/' + entry['name'], source=str(source)))
            wrapper = self.directory / 'lean-wrapper.sh'
            wrapper.write_text('#!/bin/bash\nexport LEAN_PATH=' + ':'.join(paths)
                               + ':/work/objects\nexec /opt/lean/bin/lean -j2 "$@"\n')
            wrapper.chmod(0o555)
            spec['entries'].append(dict(kind='ro', path='/bin/lean', source=str(wrapper)))
            spec['env'].update(LEAN_PATH=':'.join(paths) + ':/work/objects',
                               PATH='/opt/lean/bin:/bin:/usr/bin')
        for name in ([] if ARGS.python_only else ['gcc', 'g++', 'as', 'ld']):
            executable = shutil.which(name)
            if executable:
                spec['entries'].append(dict(kind='ro', path='/usr/bin/' + name,
                                            source=str(Path(executable).resolve())))
        for name in ([] if ARGS.python_only else ['/usr/lib/gcc', '/usr/include']):
            if Path(name).is_dir():
                spec['entries'].append(dict(kind='ro', path=name, source=name))
        spec['env'].update(HOME='/home/worker', LANG='C', LC_ALL='C')
        self.spec_path.write_text(json.dumps(spec, indent=2) + '\n')
        return url

    async def freeze_work(self):
        """Stop only commands in this worker's private PID namespace before export."""
        parent = self.active_process.pid
        table = {}
        for path in Path('/proc').iterdir():
            if not path.name.isdigit():
                continue
            try:
                status = (path / 'status').read_text()
                fields = {line.split(':', 1)[0]: line.split(':', 1)[1].strip()
                          for line in status.splitlines() if ':' in line}
                table[int(path.name)] = (int(fields['PPid']),
                    [int(value) for value in fields.get('NSpid', path.name).split()])
            except (FileNotFoundError, PermissionError, ProcessLookupError):
                continue
        descendants = {parent}
        while True:
            expanded = descendants | {pid for pid, (ppid, _) in table.items()
                                      if ppid in descendants}
            if expanded == descendants:
                break
            descendants = expanded
        stopped = []
        host_namespace = os.readlink('/proc/self/ns/pid')
        for pid in sorted(descendants - {parent}):
            ids = table[pid][1]
            try:
                if os.readlink('/proc/' + str(pid) + '/ns/pid') == host_namespace:
                    continue
                if len(ids) > 1 and ids[-1] > 2:
                    os.kill(pid, signal.SIGSTOP)
                    stopped.append(dict(host_pid=pid, namespace_pid=ids[-1]))
            except (FileNotFoundError, ProcessLookupError):
                continue
        return dict(status='ASSIGNED_WORKER_COMMANDS_QUIESCED_BEFORE_EXPORT',
                    stopped=stopped, private_init_and_execserver_retained=True)


def main():
    global ARGS
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', required=True)
    parser.add_argument('--out', required=True)
    parser.add_argument('--phase', required=True)
    parser.add_argument('--wall', type=int, default=900)
    parser.add_argument('--output', type=int, default=24000)
    parser.add_argument('--operations', type=int, default=96)
    parser.add_argument('--responses', type=int, default=64)
    parser.add_argument('--memory-gib', type=int, default=48)
    parser.add_argument('--compiler', action='store_true')
    parser.add_argument('--python-only', action='store_true')
    parser.add_argument('--environment', default=str(ROOT.parent /
        'ieantn-reproducibility-20261109/.work/bootstrap-v1/ENVIRONMENT.json'))
    parser.add_argument('--fixture', action='store_true')
    parser.add_argument('--paired-task-seed', type=int, default=0)
    ARGS = parser.parse_args()
    need(not (ARGS.compiler and ARGS.python_only), 'Python-only discovery has no compiler')
    need(1 <= ARGS.memory_gib <= 300, 'invalid memory allowance')
    need(1 <= ARGS.wall <= 7200, 'invalid session wall ceiling')
    ARGS.fixture_hook_fault = False
    ARGS.python_optimization = sys.flags.optimize
    private = ROOT / 'private/controller-temp'
    private.mkdir(exist_ok=True)
    tempfile.tempdir = str(private)
    CORE.C = VENDOR
    CORE.V = VENDOR.parent
    CORE.MODEL = 'gpt-6.1-sol'
    CORE.ExistingExecutorAdapter = ResearchExecutor
    CORE.make_prompt = make_prompt
    CORE.BASE = ('You are a mathematical researcher in one fresh controlled session. '
                 'Follow the supplied task and resource policy. Use only the assigned '
                 'offline packet and generic tools. Construct the strongest valid result '
                 'you can and preserve incomplete work honestly. No delegation or external search.')
    CORE.DEVELOPER = (
        'Use only the assigned offline executor. No collaboration, MCP, connectors, '
        'browser, external network, other tasks, prior conversations or hidden files. '
        'Use non-login /bin/bash and /usr/bin/python3.10. Do not provide private reasoning '
        'transcripts; publish mathematical statements, derivations, code, tests and limitations. '
        'Keep drafts under /work/submission. Write the exact submitted file SHA256 values '
        'in LOCK.json as {"files":[{"path":"candidate.md","sha256":"..."}]}; '
        'use at most15 regular flat payload filenames plus LOCK.json, each at most2MiB. Include complete proof '
        'source where possible, exact parameters and source assumptions. Never call a '
        'numerical experiment or generated Lean source a checked theorem. The controller '
        'seals incomplete deadline drafts too. Work within the given token/time/operation '
        'budgets and finish with LOCKED after the lock. Only execution and file tools '
        'and their polling are authorized.')
    asyncio.run(CORE.main(ARGS))


if __name__ == '__main__':
    main()
