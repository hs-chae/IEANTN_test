#!/usr/bin/env python3
"""Check exact report Git permalinks against the pinned publication objects."""
from pathlib import Path
import argparse, hashlib, html, json, os, re, subprocess, urllib.parse


def need(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--network', type=Path, required=True)
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    need(not a.out.exists(), 'fresh receipt')
    rows = []
    for raw in re.findall(r'href="([^"]+)"', a.input.read_text()):
        url = html.unescape(raw)
        u = urllib.parse.urlparse(url)
        if u.netloc != 'github.com' or '/blob/' not in u.path:
            continue
        owner, repo, _, commit, *rest = u.path.strip('/').split('/')
        path = urllib.parse.unquote('/'.join(rest))
        cp = subprocess.run(['git', 'cat-file', '-e', commit + ':' + path], cwd=a.network,
                            capture_output=True, text=True)
        need(cp.returncode == 0, 'pinned Git path absent: ' + url)
        body = subprocess.check_output(['git', 'show', commit + ':' + path], cwd=a.network)
        rows.append({'url': url, 'repository': owner + '/' + repo, 'commit': commit,
                     'path': path, 'bytes': len(body),
                     'git_blob_content_sha256': hashlib.sha256(body).hexdigest()})
    need(len(rows) == 17, 'exact17 Git source links')
    need({r['commit'] for r in rows} == {'a8b2d5631c7e6de5bfdf2b7d576633fcb11eab56'}, 'exact source pin')
    matches = []
    for remote in subprocess.check_output(['git', 'remote'], cwd=a.network, text=True).splitlines():
        raw = subprocess.check_output(['git', 'remote', 'get-url', remote], cwd=a.network, text=True).strip()
        if raw.startswith('git@github.com:'):
            repo = raw.split(':', 1)[1].removesuffix('.git')
        else:
            repo = urllib.parse.urlparse(raw).path.strip('/').removesuffix('.git')
        if repo == 'hs-chae/IEANTN_test':
            matches.append(remote)
    need(bool(matches), 'publication repository does not match a configured remote')
    result = {'status': 'PASS_ALL17_EXACT_PINNED_GIT_PATHS_EXIST', 'rows': rows,
              'matching_publication_remotes': matches,
              'report_sha256': hashlib.sha256(a.input.read_bytes()).hexdigest(),
              'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'scope': 'Local Git object/path existence for the configured publication repository; Root separately verified actual remote push. No unauthenticated HTTP fetch claim.'}
    pending = a.out.with_name('.' + a.out.name + '.pending')
    pending.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(pending, a.out)
    print(result['status'])


if __name__ == '__main__':
    main()
