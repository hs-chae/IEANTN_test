# Integration controller acceptance study

This is a bounded validation study of the integration command line. It changes no
Lean statement, mathematical assumption, C program, algorithm, parameter or
numerical output. It is not source-first PV and does not change primary outcomes.

## Original finding and its precise impact

The original controller SHA is
`9b630a9fec993749d6fefdf81dd7893cac2b4f674392be21eb385c1fecd106e6`.
Its optional historical `--resource-replay` branch checked the 23 object hashes
and strict integer return codes. It accepted changed stored bytes in
`source/RamanujanPV/FiniteLogSource.lean` and
`logs/RamanujanPV.FiniteLogSource.stdout`, even though their BUILD hashes were
unchanged. Both mutations were accepted by actual normal, -O and -OO CLI runs.
The same original kernel objects were still used. This is missing provenance
revalidation of historical artifacts, not a mathematical counterexample.
The clean resource-complete 261-module route does not use that optional branch.

The original 63-route matrix contains three positive checks, 54 expected
rejections and six unexpected acceptances (two fixtures in three modes). Every
retained original source/bank file checked at that time, 2048 files, was unchanged.
`receipts/ORIGINAL_FINDING.json` records exact paths, hashes and triggers.

## Private repair and actual proof consumer

`guard.patch` changes only the optional legacy branch. The prefix before it and
the suffix containing the clean path and Lean consumer loop are byte-identical.
The intermediate repaired controller SHA is
`4374e647a008568d2450fe5c46354cebacdf109866072db6445500f9c8078dbf`.
It binds the fixed 23-module order, stored/current source bytes, object hashes,
stdout/stderr, axiom audits, actual C include, executed controller and basis joins.

All 63 original routes pass under this private repair: three positive checks and
60 expected rejections. Another 30 actual CLI tests cover the new stderr, C,
controller, receipt-field, order and BUILD-status guards in all three modes.
These are 93 actual routes, not import-only tests.

One authorized actual 24-source legacy replay passed in 108.795854 seconds,
with peak child RAM 7,949,264 KiB, 11,550,149 final owned bytes and zero accepted
child OOM events. It reused the hash-bound fresh 261+55 source foundations and
corrected 23-module objects; it was not another cold 340-source build. All 17
scoped theorem roots and 61 printed support audits use only propext,
Classical.choice and Quot.sound. All 48 raw compiler stdout/stderr files and
executed controller bytes are preserved here.

The final private controller additionally refuses an unnecessary
`--resource-replay` argument when the basis is already resource-complete. Such
an override previously skipped legacy validation but could still be used by the
consumer loop. The flag is reserved for historical two-stage bases. This one-line
policy guard changes no supported clean or historical numerical algorithm.

Final controller SHA:
`857ba8bf9f670e5df415dba16c84cf72c3168c6aa49df0cf1649bdd7f1d404cf`.
Its own 93 legacy CLI routes pass. One final-hash actual 24-source legacy replay
passed in 114.676987 seconds, peak child RAM 7,952,416 KiB, 11,551,376 final owned
bytes, zero accepted child OOM events. All17 scoped roots and61 printed support
audits use only the standard three axioms. The intermediate controller/run is
retained as history; the final controller, combined/addition patches, 48 new raw
compiler logs and receipts are included separately. The latest full reproduction
wrapper targets this final controller.

## Locked specification versus receipts

The source manifests are approved inputs. Removing an `original_path` from that
trusted specification is not an inner-controller bug. The actual outer packet
verifier was invoked from the unchanged accepted packet: three positive modes
passed and three private omitted-pin fixtures were rejected by the manifest
hash/size check. All 3095 original packet files remained unchanged. The six-route
outer receipt is included; the original verifier/tree was not modified.

## Reproduction

Python 3.11.14 and the standard library suffice for the CLI controls. Use the
parent study's pinned-source recipes to regenerate the 261, 23 and 55 numerical/
proof banks and preserve the fixed source tree. From this directory, run:

```sh
PYTHONDONTWRITEBYTECODE=1 python reproduce.py \
  --network /path/to/approved/network \
  --pi /path/to/source-rebuilt261 \
  --resources /path/to/source-rebuilt23 \
  --spectral /path/to/source-rebuilt55 \
  --out /data/ivy-rh-limit-20261122/reviews/integration-cli/fresh-reproduction
```

The output must be a fresh experiment-owned directory. The wrapper verifies all
locked source inputs, uses the exact original/repaired controller bytes, and
never changes the supplied source or bank directories. In private fixture copies
only, it selects the legacy resource policy and rebases receipt links. This also
lets a freshly generated resource-complete prefix exercise the historical guard;
it does not relabel the source experiment or alter its mathematical outputs.
The original six acceptances and repaired 93-route result have been reproduced
through this wrapper; its receipt is included. Every mutation first replaces its
hardlinked file with a fresh private inode. Bytecode writes are disabled.

`receipts/LEGACY24_COMMAND.json` records the actual compiled-consumer command and
pinned generic context. The parent README supplies the clean generic bootstrap.
No random seed is used. Acceptance uses explicit errors and strict parsing;
no check relies on assert, __debug__ or Python optimization.

## Final validation status

The actual newly rebuilt resource-complete261 plus new55 spectral banks also
passed all six final-controller policy checks: three normal/-O/-OO clean
preflights without the resource flag, and three refusals of a supplied legacy
resource flag. All1381 retained bank files stayed unchanged. These checks used
the genuine new clean policy, not the private counterfactual fixture policy.
`check_clean_routes.py` and its complete commands/stdout/stderr receipt are included.

The final controller therefore has93 legacy-route tests,6 actual clean-route
tests and6 outer packet tests, with the historical six acceptances retained
separately. No source-first PV or new mathematical claim is made by this testing.
Root has reviewed the exact final patch and is responsible for applying it to
current source after the original full packet replay, then performing the new
actual clean24 proof replay and publication. This export contains the completed
private legacy24 final-hash replay; that distinction is explicit in every receipt.
The final updated HTML browser review is a separate final-report evidence folder.
