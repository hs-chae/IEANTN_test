#!/bin/bash
# Run via /bin/bash (non-login). Optional argument must be fresh and under /work.
set -eu
dst=${1:-/work/review-c005-reproduction}
case "$dst" in /work/*) ;; *) exit 2 ;; esac
/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out "$dst"
(
  cd "$dst"
  /usr/bin/python3.10 -B replay.py
)
cd /work/submission
/usr/bin/python3.10 -B audit.py "$dst"
