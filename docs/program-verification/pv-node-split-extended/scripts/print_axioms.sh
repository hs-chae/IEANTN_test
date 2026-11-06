#!/usr/bin/env bash
# print_axioms.sh <solution-dir> <module> <decl>...   `#print axioms` for each decl, importing <module> with the
# solution's own build directory first on LEAN_PATH (several solution packages root a module named `Solution`).
set -u
DIR=$1; MOD=$2; shift 2
cd "$DIR" || exit 2
LP=$(lake env printenv LEAN_PATH 2>/dev/null)
F=$(mktemp --suffix=.lean -p /tmp/claude-1013/-ryu-hyunsik-playground-independence-alex/75718ac3-268c-412a-8046-11dd54eef723/scratchpad)
{ echo "import $MOD"; for n in "$@"; do echo "#print axioms $n"; done; } > $F
LEAN_PATH="$DIR/.lake/build/lib/lean:$LP" timeout 900 lean $F 2>&1 | tr '\n' ' ' | sed 's/'"'"'[A-Za-z0-9_.]*'"'"' depends on axioms:/\n&/g'; echo
rm -f $F
