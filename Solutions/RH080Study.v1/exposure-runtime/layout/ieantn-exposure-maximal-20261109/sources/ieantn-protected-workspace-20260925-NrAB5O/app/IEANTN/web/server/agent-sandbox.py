# Copyright (c) 2026 IEANTN contributors. Apache 2.0 (../../LICENSE).
"""Fail-closed Linux confinement for native Codex/Claude processes.

The workbench starts this helper as
    unshare --user --map-root-user --mount --propagation private -- python3 -I -B agent-sandbox.py <spec.json>
so it already runs inside fresh user and mount namespaces (uid 0 there, the
caller's real uid outside). It then builds a private tmpfs root that contains
ONLY the paths listed in the spec, pivots into it, creates a pid namespace,
mounts a private /proc, maps back to the caller's real uid with every
capability dropped and no_new_privs set, and finally executes the agent.

Every step is verified; any failure exits with status 125 BEFORE the agent
starts, printing "IEANTN isolation setup failed: ..." on stderr. Nothing here
reads or copies credentials: credential files are made visible to the agent
only through the same bind mounts the spec names.

Process tree (host view): node -> [unshare exec'd into] python (this file,
outer) -> python (pid 1 of the new pid namespace: signal forwarder/reaper)
-> agent (nested user namespace, real uid, no capabilities).
"""
import ctypes
import errno
import json
import os
import platform
import signal
import stat
import sys
import traceback

libc = ctypes.CDLL(None, use_errno=True)
MS_RDONLY, MS_NOSUID, MS_NODEV, MS_NOEXEC, MS_REMOUNT, MS_BIND, MS_REC, MS_PRIVATE = 1, 2, 4, 8, 32, 4096, 16384, 1 << 18
MNT_DETACH = 2
CLONE_NEWUSER, CLONE_NEWPID = 0x10000000, 0x20000000
PR_SET_PDEATHSIG, PR_SET_NO_NEW_PRIVS = 1, 38
FLAG_NAMES = {'ro': MS_RDONLY, 'nosuid': MS_NOSUID, 'nodev': MS_NODEV, 'noexec': MS_NOEXEC, 'noatime': 1024, 'nodiratime': 2048, 'relatime': 1 << 21, 'strictatime': 1 << 24, 'sync': 16, 'dirsync': 128, 'mand': 64, 'lazytime': 1 << 25, 'nosymfollow': 256}
PIVOT_ROOT = {'x86_64': 155, 'aarch64': 41, 'riscv64': 41, 'i686': 217, 'i386': 217, 's390x': 217, 'ppc64le': 203}
FAILURE_STATUS = 125


class SetupError(Exception):
    pass


def fail(message):
    sys.stderr.write(f'IEANTN isolation setup failed: {message}\n')
    sys.stderr.flush()
    os._exit(FAILURE_STATUS)


def check(rc, what):
    if rc != 0:
        code = ctypes.get_errno()
        raise SetupError(f'{what}: {os.strerror(code)} (errno {code})')


def mount(source, target, fstype, flags, data=None):
    check(libc.mount(source.encode() if source else None, target.encode(), fstype.encode() if fstype else None, ctypes.c_ulong(flags), data.encode() if data else None), f'mount {source or fstype} on {target}')


def unescape(field):
    return field.replace('\\040', ' ').replace('\\011', '\t').replace('\\012', '\n').replace('\\134', '\\')


def mountinfo():
    """Return {mount point: option string} for the current mount namespace."""
    table = {}
    with open('/proc/self/mountinfo') as handle:
        for line in handle:
            parts = line.split()
            table[unescape(parts[4])] = parts[5]
    return table


def mount_flags(target):
    options = mountinfo().get(target)
    if options is None:
        raise SetupError(f'mount not found after binding: {target}')
    flags = 0
    for option in options.split(','):
        flags |= FLAG_NAMES.get(option, 0)
    return flags


def validated_path(value, what):
    if not isinstance(value, str) or not value or not value.startswith('/') or '\0' in value:
        raise SetupError(f'{what} must be an absolute path')
    if os.path.normpath(value) != value or any(part == '..' for part in value.split('/')):
        raise SetupError(f'{what} must be normalized: {value}')
    return value


class Sandbox:
    def __init__(self, spec):
        if not isinstance(spec, dict) or spec.get('version') != 1:
            raise SetupError('unsupported spec version')
        self.root = validated_path(spec.get('root'), 'root')
        self.cwd = validated_path(spec.get('cwd'), 'cwd')
        self.uid, self.gid = spec.get('uid'), spec.get('gid')
        if not isinstance(self.uid, int) or not isinstance(self.gid, int) or self.uid <= 0 or self.gid <= 0:
            raise SetupError('uid/gid must be positive integers (never root)')
        self.command = spec.get('command')
        self.network = spec.get('network', 'inherited')
        self.terminal = spec.get('terminal', False)
        if not isinstance(self.terminal, bool):
            raise SetupError('terminal must be boolean')
        if self.network not in ('inherited', 'offline'):
            raise SetupError('unsupported network policy')
        if not isinstance(self.command, list) or not self.command or not all(isinstance(a, str) for a in self.command):
            raise SetupError('command must be a non-empty list of strings')
        self.env = spec.get('env')
        if not isinstance(self.env, dict) or not all(isinstance(k, str) and isinstance(v, str) and '=' not in k and '\0' not in k + v for k, v in self.env.items()):
            raise SetupError('env must map names to strings')
        entries = spec.get('entries')
        if not isinstance(entries, list):
            raise SetupError('entries must be a list')
        self.entries = []
        for entry in entries:
            kind, target = entry.get('kind'), validated_path(entry.get('path'), 'entry path')
            if kind not in ('ro', 'rw', 'mask', 'copy', 'dir'):
                raise SetupError(f'unknown entry kind {kind!r}')
            if target == '/' or target.startswith(self.root + '/') or target == self.root:
                raise SetupError(f'entry may not name the root or the sandbox mount point: {target}')
            if entry.get('source') is not None:
                if kind not in ('ro', 'rw', 'copy'):
                    raise SetupError(f'{kind} entries cannot have a source: {target}')
                validated_path(entry['source'], 'entry source')
            self.entries.append((target, kind, entry))
        # Parents strictly before children, so nested binds land on already mounted parents.
        self.entries.sort(key=lambda item: (item[0].count('/'), item[0]))
        self.tmpfs_size = str(spec.get('tmpfsSize', '256m'))
        self.tmp_size = str(spec.get('tmpSize', '1g'))
        if not all(size.isalnum() for size in (self.tmpfs_size, self.tmp_size)):
            raise SetupError('tmpfs sizes must be plain values such as 256m')
        self.read_only_targets = []
        self.masks = 0
        self.root_dev = None
        self.private_devs = set()

    def private_tmpfs(self, place, flags, options):
        mount('tmpfs', place, 'tmpfs', flags, options)
        self.private_devs.add(os.lstat(place).st_dev)

    # -- tmpfs skeleton -------------------------------------------------------------------------
    def ensure_dir(self, target):
        """Create directories on our own tmpfs mounts only; never create inside a bound host tree."""
        cursor = self.root
        for part in [p for p in target.split('/') if p]:
            cursor = os.path.join(cursor, part)
            try:
                info = os.lstat(cursor)
            except FileNotFoundError:
                if os.lstat(os.path.dirname(cursor)).st_dev not in self.private_devs:
                    raise SetupError(f'refusing to create {cursor} inside a bound host directory')
                os.mkdir(cursor, 0o755)
                continue
            if stat.S_ISLNK(info.st_mode):
                raise SetupError(f'symlink in sandbox skeleton: {cursor}')
            if not stat.S_ISDIR(info.st_mode):
                raise SetupError(f'not a directory in sandbox skeleton: {cursor}')
        return cursor

    def ensure_file(self, target):
        parent = self.ensure_dir(os.path.dirname(target))
        cursor = os.path.join(parent, os.path.basename(target))
        try:
            info = os.lstat(cursor)
            if stat.S_ISLNK(info.st_mode) or stat.S_ISDIR(info.st_mode):
                raise SetupError(f'cannot place a file over {cursor}')
        except FileNotFoundError:
            if os.lstat(parent).st_dev not in self.private_devs:
                raise SetupError(f'refusing to create {cursor} inside a bound host directory')
            fd = os.open(cursor, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
            os.close(fd)
        return cursor

    def remount_read_only(self, target):
        mount(None, target, None, MS_REMOUNT | MS_BIND | MS_RDONLY | mount_flags(target))
        self.read_only_targets.append(target)

    def bind(self, host, target, read_only):
        info = os.lstat(host)
        if stat.S_ISLNK(info.st_mode):
            if host != target:
                raise SetupError(f'a bind source may not be a symlink: {host}')
            # Merged-usr systems: replicate /bin -> usr/bin instead of binding through the link.
            link = os.readlink(host)
            place = os.path.join(self.ensure_dir(os.path.dirname(target)), os.path.basename(target))
            if not os.path.lexists(place):
                os.symlink(link, place)
            return
        if stat.S_ISDIR(info.st_mode):
            place = self.ensure_dir(target)
        elif stat.S_ISREG(info.st_mode):
            place = self.ensure_file(target)
        else:
            raise SetupError(f'only directories and regular files can be bound: {host}')
        mount(host, place, None, MS_BIND)
        if read_only:
            self.remount_read_only(place)

    def scratch(self, name, content=None):
        """Create an empty file (or a private copy) on the private mask tmpfs."""
        path = os.path.join(self.root, '.masks', f'{self.masks}-{name}')
        self.masks += 1
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        try:
            if content is not None:
                os.write(fd, content)
        finally:
            os.close(fd)
        return path

    def mask(self, target):
        """Hide a host object below an already bound tree with an empty, writable, ephemeral object."""
        place = os.path.join(self.root, target.lstrip('/'))
        try:
            info = os.lstat(place)
        except FileNotFoundError:
            return
        if stat.S_ISDIR(info.st_mode):
            self.private_tmpfs(place, MS_NOSUID | MS_NODEV, 'mode=0700,size=16m')
        elif stat.S_ISREG(info.st_mode):
            mount(self.scratch('mask'), place, None, MS_BIND)
        else:
            raise SetupError(f'cannot mask a special file or symlink: {target}')

    def copy(self, host, target):
        """Expose a private, discardable copy of a host file (writes never reach the host)."""
        try:
            with open(host, 'rb') as handle:
                content = handle.read(8_000_000)
                if handle.read(1):
                    raise SetupError(f'file too large to copy into the sandbox: {host}')
        except FileNotFoundError:
            return
        place = os.path.join(self.root, target.lstrip('/'))
        if not os.path.lexists(place):
            # The target lives on our own tmpfs (e.g. the private home): a plain private file lets
            # the program rewrite it with the usual temp-file-and-rename pattern, which a bind mount
            # would refuse with EBUSY. Nothing written there reaches the host.
            parent = self.ensure_dir(os.path.dirname(target))
            if os.lstat(parent).st_dev not in self.private_devs:
                raise SetupError(f'refusing to create a copy inside a bound host directory: {target}')
            fd = os.open(place, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
            try:
                os.write(fd, content)
            finally:
                os.close(fd)
            return
        if not stat.S_ISREG(os.lstat(place).st_mode):
            raise SetupError(f'cannot place a copy over {target}')
        # Inside a bound host directory the real file is shadowed by a private copy.
        mount(self.scratch('copy', content), place, None, MS_BIND)

    def devices(self):
        dev = self.ensure_dir('/dev')
        self.private_tmpfs(dev, MS_NOSUID | MS_NOEXEC, 'mode=0755,size=4m')
        # /dev/tty is included because Codex's bundled bwrap sandbox insists on binding it; the
        # program runs detached without a controlling terminal, so opening it fails harmlessly.
        for name in ('null', 'zero', 'full', 'random', 'urandom', 'tty'):
            host = '/dev/' + name
            if not os.path.exists(host):
                if name == 'tty':
                    continue
                raise SetupError(f'missing device {host}')
            place = os.path.join(dev, name)
            os.close(os.open(place, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o666))
            mount(host, place, None, MS_BIND)
        for name, link in (('fd', '/proc/self/fd'), ('stdin', '/proc/self/fd/0'), ('stdout', '/proc/self/fd/1'), ('stderr', '/proc/self/fd/2')):
            os.symlink(link, os.path.join(dev, name))
        if self.terminal:
            # A separate PTY instance; never bind the host's /dev/pts or inherit its terminal.
            pts = os.path.join(dev, 'pts')
            os.mkdir(pts, 0o755)
            mount('devpts', pts, 'devpts', MS_NOSUID | MS_NOEXEC, 'newinstance,ptmxmode=0666,mode=0600')
            os.symlink('pts/ptmx', os.path.join(dev, 'ptmx'))
        shm = os.path.join(dev, 'shm')
        os.mkdir(shm, 0o1777)
        self.private_tmpfs(shm, MS_NOSUID | MS_NODEV, 'mode=1777,size=64m')

    def build(self):
        if os.uname().sysname != 'Linux':
            raise SetupError('Linux namespaces are required')
        if platform.machine() not in PIVOT_ROOT:
            raise SetupError(f'unsupported architecture {platform.machine()}')
        if self.network == 'offline':
            # Backend foundation: no host loopback, interfaces, routing or Internet.
            # Its test UI transport is an explicitly mounted private Unix socket.
            previous = os.readlink('/proc/self/ns/net')
            check(libc.unshare(0x40000000), 'private offline network namespace')
            if os.readlink('/proc/self/ns/net') == previous:
                raise SetupError('network namespace did not change')
        root_info = os.lstat(self.root)
        if not stat.S_ISDIR(root_info.st_mode) or os.listdir(self.root):
            raise SetupError('sandbox mount point must be an empty directory')
        self.private_tmpfs(self.root, MS_NOSUID | MS_NODEV, f'mode=0755,size={self.tmpfs_size}')
        self.root_dev = os.lstat(self.root).st_dev
        masks = os.path.join(self.root, '.masks')
        os.mkdir(masks, 0o700)
        self.private_tmpfs(masks, MS_NOSUID | MS_NODEV | MS_NOEXEC, 'mode=0700,size=32m')
        # A new procfs may only be mounted while the host's /proc is still visible in
        # this mount namespace, so it happens here, before pivot, from inside the new pid
        # namespace: the instance then shows only sandbox processes.
        proc = os.path.join(self.root, 'proc')
        os.mkdir(proc, 0o555)
        mount('proc', proc, 'proc', MS_NOSUID | MS_NODEV | MS_NOEXEC)
        if not os.path.isdir(os.path.join(proc, str(os.getpid()))) or os.getpid() != 1:
            raise SetupError('private /proc does not belong to the new pid namespace')
        tmp = self.ensure_dir('/tmp')
        os.chmod(tmp, 0o1777)
        self.private_tmpfs(tmp, MS_NOSUID | MS_NODEV, f'mode=1777,size={self.tmp_size}')
        self.devices()
        for target, kind, entry in self.entries:
            if kind == 'dir':
                place = self.ensure_dir(target)
                if os.lstat(place).st_dev == self.root_dev:
                    os.chmod(place, int(entry.get('mode', 0o700)))
            elif kind in ('ro', 'rw'):
                host = entry.get('source') or target
                if not os.path.lexists(host):
                    if entry.get('optional'):
                        continue
                    raise SetupError(f'required path is missing on this computer: {host}')
                self.bind(host, target, kind == 'ro')
            elif kind == 'mask':
                self.mask(target)
            elif kind == 'copy':
                self.copy(entry.get('source') or target, target)
        if not os.path.isdir(os.path.join(self.root, self.cwd.lstrip('/'))):
            raise SetupError(f'working directory is not inside the sandbox: {self.cwd}')

    # -- pivot and verification -----------------------------------------------------------------
    def pivot(self):
        os.chdir(self.root)
        # pivot_root(".", ".") followed by a lazy unmount of the old root needs no put_old
        # directory and leaves nothing of the host tree reachable (pivot_root(2), NOTES).
        check(libc.syscall(PIVOT_ROOT[platform.machine()], b'.', b'.'), 'pivot_root')
        check(libc.umount2(b'.', MNT_DETACH), 'detach old root')
        os.chdir('/')
        if os.stat('/').st_dev != self.root_dev:
            raise SetupError('root is not the private tmpfs after pivot')

    def verify(self):
        """Run inside the pid namespace after pivot; /proc is the private instance."""
        table = mountinfo()
        if '/' not in table or 'ro' in table['/'].split(','):
            raise SetupError('unexpected root mount state')
        for target in self.read_only_targets:
            inside = target[len(self.root):] or '/'
            options = table.get(inside)
            if options is None or 'ro' not in options.split(','):
                raise SetupError(f'read-only bind is not read-only: {inside}')
        for point in table:
            if point.startswith('/.old_root'):
                raise SetupError('old root still mounted')
        if not os.path.isdir('/proc/1'):
            raise SetupError('private /proc missing')


def forward_signals(child):
    def handler(signum, _frame):
        try:
            os.kill(child, signum)
        except ProcessLookupError:
            pass
    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGUSR1, signal.SIGUSR2, signal.SIGQUIT):
        signal.signal(signum, handler)


def wait_for(child):
    """Reap until the given child exits; return a shell-style exit status."""
    while True:
        try:
            pid, status = os.wait()
        except ChildProcessError:
            return FAILURE_STATUS
        except InterruptedError:
            continue
        if pid != child:
            continue
        if os.WIFEXITED(status):
            return os.WEXITSTATUS(status)
        if os.WIFSIGNALED(status):
            return 128 + os.WTERMSIG(status)


def run_agent(sandbox):
    """Grandchild: map back to the real uid, drop everything, exec."""
    check(libc.unshare(CLONE_NEWUSER), 'nested user namespace')
    for name, value in (('setgroups', b'deny'), ('gid_map', f'{sandbox.gid} 0 1'.encode()), ('uid_map', f'{sandbox.uid} 0 1'.encode())):
        fd = os.open(f'/proc/self/{name}', os.O_WRONLY)
        try:
            os.write(fd, value)
        finally:
            os.close(fd)
    if os.getuid() != sandbox.uid or os.getgid() != sandbox.gid:
        raise SetupError('uid mapping did not apply')
    check(libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0), 'no_new_privs')
    os.chdir(sandbox.cwd)
    os.execvpe(sandbox.command[0], sandbox.command, sandbox.env)


def main():
    if len(sys.argv) != 2:
        fail('usage: agent-sandbox.py <spec.json>')
    try:
        with open(sys.argv[1], 'rb') as handle:
            spec = json.loads(handle.read(4_000_000))
        sandbox = Sandbox(spec)
        if os.getuid() != 0 or os.getgid() != 0:
            raise SetupError('not running as the user-namespace root; start through unshare --user --map-root-user')
        # If the workbench process disappears, take the whole sandbox down with it.
        check(libc.prctl(PR_SET_PDEATHSIG, signal.SIGKILL, 0, 0, 0), 'parent death signal')
        check(libc.unshare(CLONE_NEWPID), 'pid namespace')
    except SetupError as error:
        fail(str(error))
    except Exception:  # noqa: BLE001 - any unexpected error must stop before the agent starts
        fail(traceback.format_exc().strip().splitlines()[-1])
    init = os.fork()
    if init == 0:
        try:
            check(libc.prctl(PR_SET_PDEATHSIG, signal.SIGKILL, 0, 0, 0), 'parent death signal')
            if os.getpid() != 1:
                raise SetupError('pid namespace init is not pid 1')
            # The mount namespace is shared with the outer process: all mounts and the
            # pivot below apply to both, while /proc reflects this new pid namespace.
            sandbox.build()
            sandbox.pivot()
            sandbox.verify()
            agent = os.fork()
            if agent == 0:
                try:
                    run_agent(sandbox)
                except SetupError as error:
                    fail(str(error))
                except Exception:  # noqa: BLE001
                    fail(traceback.format_exc().strip().splitlines()[-1])
            forward_signals(agent)
            os._exit(wait_for(agent))
        except SetupError as error:
            fail(str(error))
        except Exception:  # noqa: BLE001
            fail(traceback.format_exc().strip().splitlines()[-1])
    forward_signals(init)
    os._exit(wait_for(init))


if __name__ == '__main__':
    main()
