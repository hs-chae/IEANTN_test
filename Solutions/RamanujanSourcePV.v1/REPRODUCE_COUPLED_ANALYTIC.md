# Coupled-error analytic continuation

The completed Lean proof gives the actual IEANTN Ramanujan gap greater than
6,000,000,000,000 for every real input at least 1,250,000,000,000. It has exactly
25 explicit source/analytic inputs: the original 24 plus the one-sided theta
bound in Büthe's final Theorem 2, equation (1.6). That additional conclusion is
already recorded by IEANTN as `Buthe.v1.theorem_2_theta`; the paper's arXiv
version 2 is distinct from the network's `Buthe.v2` Lemma 3 variant.

The original 24-input ray, all original numerical arrays, the 1.49T locked count
candidate and its running verification remain unchanged. No optimality or
best-known-bound claim is made. The endpoint decreases by 16.10738255%; the
length of the prospective finite interval from the fixed original starting
point decreases by 16.53301148%. Neither percentage is a measured runtime gain.
The shorter full finite certificate is still missing.

The mechanism is to retain the SAME theta-error integral in both prime-count
bounds. The exact partial-summation normalization constant is kept through the
anchor calculation and cancels when that shared integral receives its proved
upper bound. The mathematical endpoint uses four 200-term Taylor inequalities
proved in the kernel. These are ordinary kernel analytic proofs, not a claim
of source-first C program verification. The original finite C-program PV
results retain their separate scope and trust boundaries.

Read the standalone offline report in
`evidence/coupled-final-independent-v2/REPORT.html` for rendered equations,
primary-source locators and the independent type/dependency audit. The new
explicit literature input is at
[arXiv1511.02032v2, page 2, Theorem 2, equation (1.6)](https://arxiv.org/pdf/1511.02032v2).
Its pinned PDF SHA-256 is
`350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1`.
This published computational theorem remains a literature-backed input; its
original computational implementation is not claimed formally verified here.

## Reproduce from clean application objects

Use the matching research checkout containing every source hash in
`evidence/coupled-analytic-1250-v1/SOURCE_LOCK.json`. Linux x86-64, Python 3.11+,
Git, Elan and the root repository's pinned Lake dependencies are required.
Lean is 4.34.0-rc2, with binary SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`;
Mathlib is `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.

From the repository root obtain the pinned generic libraries with
`lake exe cache get`. Then, from this solution directory, run:

```sh
python3 scripts/bootstrap_context.py \
  --out /data/ivy-ramanujan-source-pv-20261119/coupled-clean-context.json
python3 scripts/reproduce_coupled_analytic.py \
  --context /data/ivy-ramanujan-source-pv-20261119/coupled-clean-context.json \
  --out /data/ivy-ramanujan-source-pv-20261119/coupled-clean-replay \
  --jobs 2 --cpus 8,9 --memory-gib 48 --aggregate-gib 96 \
  --host-reserve-gib 512
```

Choose fresh output/context filenames. The script checks every one of the 673
original source hashes before dispatch. It rebuilds the entire selected
application closure into a fresh private object bank, including the independent
exact-25-input type audit, the shorter conditional finite-certificate assembly
and the stronger analytic margin. Only pinned generic libraries are reused;
no previous application proof objects or numerical outputs are imported.
The Taylor endpoint proofs regenerate their arithmetic inside Lean. No prime
list, prime-count data, random seed or external numerical array is needed.

The guarded helper passed 33 actual normal/`-O`/`-OO` CLI controls, including
successful proof builds, clean signal drains, malformed inputs and a failed
proof while another active compiler's successful receipt was preserved. The
full cold replay remains a separate run: consult its actual final receipt;
planning or a partial checkpoint does not establish completion.

For this resource-controlled study the helper requires genuinely available
1 TiB RAM, a 512 GiB host reserve, independently 1 TiB free disk, and at most
300 GiB total experiment-owned scratch including a 3 GiB forecast. It checks
live resources, pauses new dispatch while resources are low, and drains current
work on SIGUSR1/SIGTERM/SIGINT. It does not kill active compilers. Exact commands,
resource observations, per-compiler time/RSS and source/object/log hashes are
retained. Address-space limits are not observed RAM usage.

Final acceptance is atomic and requires every module plus the final selected
axiom audit. Independently read it back with:

```sh
python3 -OO scripts/reproduce_guarded_coupled_closure.py \
  --check /data/ivy-ramanujan-source-pv-20261119/coupled-clean-replay
```

A `CHECKPOINT.json` or `RUN_STATE.json` is not final acceptance. The proof has
only the standard `propext`, `Classical.choice` and `Quot.sound` dependencies;
there is no new axiom, admitted proof or native execution axiom on the selected
conclusion. The full source-linked finite prime-count work remains open, and
is not replaced by this analytic result.
