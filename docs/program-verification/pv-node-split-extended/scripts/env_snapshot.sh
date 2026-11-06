#!/usr/bin/env bash
# Print a frozen-environment snapshot: refs, toolchain, host resources. Read-only.
B=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB
N=$B/network
echo "## snapshot $(date -u +%FT%TZ)"
echo "host $(hostname) | $(nproc) cores | $(uptime | sed 's/.*load average/load average/')"
free -g | sed 's/^/    /'
df -h /ryu / | sed 's/^/    /'
swapon --show | sed 's/^/    /'
echo "lean-toolchain $(cat $N/lean-toolchain) | $(cd $N && lake --version 2>&1 | head -1) | $(gcc --version | head -1)"
echo "python (ieantn venv) $($B/tools/bin/python --version 2>&1), PyYAML $($B/tools/bin/python -c 'import yaml;print(yaml.__version__)')"
echo "mathlib rev $(python3 -c "import json;print([p['rev'] for p in json.load(open('$N/lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")"
for r in refs/remotes/upstream/main refs/remotes/origin/main refs/remotes/origin/QRH_phase2 refs/remotes/origin/qrh-2pv refs/remotes/origin/qrh-2pv_B refs/heads/agentB/pv-node-split refs/heads/agentB/pv-node-split-exp; do
  echo "ref $r $(git -C $N rev-parse $r) $(git -C $N log -1 --format=%cI $r)"; done
for w in $(git -C $N worktree list --porcelain | awk '/^worktree/{print $2}'); do
  echo "worktree $w $(git -C $w rev-parse HEAD) $(git -C $w rev-parse --abbrev-ref HEAD) dirty_tracked=$(git -C $w status --porcelain --untracked-files=no | wc -l) untracked=$(git -C $w status --porcelain | grep -c '^??')"; done
A=/ryu/hyunsik/playground/independence/codex/ivy
for w in $A/qrh-full-network-sprint-20261105/network $A/qrh-three-stage-recovery-20261105/network $A/qrh-pv-evolution-20261104/network $A/qrh-scoped-winner-20261104/network; do
  echo "agentA $w $(git -C $w rev-parse HEAD) $(git -C $w rev-parse --abbrev-ref HEAD) $(git -C $w log -1 --format=%cI) dirty_tracked=$(git -C $w status --porcelain --untracked-files=no | wc -l)"; done
