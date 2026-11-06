#!/usr/bin/env bash
# setup_world.sh <A|B>: disposable worktree agentB/pv8_wt<X> on local branch agentB/pv8-<X> at 3280a3c (qrh-2pv_B).
# Local only: the branch has no upstream and must never be pushed. Mathlib and the other Lake packages are
# shared read-only with agentB/network through symlinks, so nothing is fetched from the network.
set -euo pipefail
X=$1; B=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB; N=$B/network; W=$B/pv8_wt$X
git -C $N worktree add -b agentB/pv8-$X $W 3280a3c3e0268578f0dbd4a0d8385f4d36877327
git -C $W branch --unset-upstream 2>/dev/null || true
mkdir -p $W/.lake && ln -s $N/.lake/packages $W/.lake/packages
for d in $(cd $W && ls -d Solutions/*/ pilots/*/ 2>/dev/null); do
  if [ -f "$W/$d/lakefile.toml" ] || [ -f "$W/$d/lakefile.lean" ]; then mkdir -p $W/$d/.lake && ln -sfn $N/.lake/packages $W/$d/.lake/packages; fi
done
echo "world $X ready at $W ($(git -C $W rev-parse --short HEAD), branch $(git -C $W rev-parse --abbrev-ref HEAD), upstream: $(git -C $W rev-parse --abbrev-ref @{u} 2>/dev/null || echo none))"
