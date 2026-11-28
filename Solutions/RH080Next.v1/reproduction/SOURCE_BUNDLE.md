# Exact campaign source selection

The selector writes a file/hash manifest. It neither creates an archive nor
marks a mathematical proof accepted. Root owns final reviewed commit selection,
compression, publication, and cleanup.

The requested universe is complete application proof/program/generator/input
source for the selected campaign, all16 locked submissions,169 common exposure
sources, and the normal canonical CLI/core scaffold. The selection rule was
written by the analytic_review agent for that request; it is not a citation or
source-facing heuristic.

The manifest includes:

- Every current project file under Solutions/RH080Next.v1, subject to the explicit
  exclusions below and final reviewed-commit byte matching. Historical and
  uncompiled sources may be present; inclusion does not claim they all compiled.
- Exact written-source unions from finite681, dual49, Gaussian92, population91,
  W4 mathematics35, common169, N24 original1033, current canonical-finite and
  final W4/canonical consumer proof plans. Module names in different files stay
  separate identities. Sources outside the project are selected by these exact
  dependency rows, rather than by copying unrelated Solutions directories.
- All13 censored LOCK payloads and all3 original admissible LOCK payloads. The
  latter are exported under ablation/review/primary_locked_payloads with original
  hashes and statuses. Prompts, event streams and historical private runtimes
  are not payload files and are not exported.
- Root dependency manifests/docs, Tools, the IEANTN core/node scaffold, and
  normal CLI scripts. The CLI's core umbrella imports its full node registry;
  this scaffold is included to preserve that real interface. Unrelated
  application Solution trees are excluded.
- Original C/header/JSON/frontend/checker sources selected by the above rules,
  including old dual C/frontend inputs and the N17/N24 fixed input bytes.

Exclusions are explicit: .git/.lake/bytecode/private memory/transcript/credential
material, compiled objects/executables, and only the enumerated regenerable
numerical artifacts. Accepted objects stay in the workspace. The34 finite CSV
files may be omitted only with the original producer, fixed witness input,
parameters and their exact expected hash inventory. N24's1020 producer Lean
files and937 CSV files are omitted only with its original producer, fixed w4
input, explicit24/8192/524288 parameters and every expected hash/import/size.
The checker-owned N24 audit is a separate generated source with the pinned
original source-cold controller and exact expected hash. These are untrusted
proposals until the separate proof and consumer gates pass.

The selector automatically reads the public681/common169/N24 inventories.
Supply actual current proof PLAN files for the other named families:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/select_source_bundle.py \
  --context /path/to/pinned-context.json --out /fresh/source-selection \
  --proof-plan dual49=/path/to/dual/PLAN.json \
  --proof-plan gaussian92=/path/to/gaussian/PLAN.json \
  --proof-plan population91=/path/to/population/PLAN.json \
  --proof-plan w4_math35=/path/to/w4-mathematics/PLAN.json \
  --proof-plan canonical_finite=/path/to/current-canonical-finite/PLAN.json \
  --proof-plan w4_actual=/path/to/actual-w4-main/PLAN.json \
  --proof-plan canonical_w4=/path/to/final-canonical-w4/PLAN.json
~~~

The plan paths may be private local receipt locations; output source names are
repository relative and no private execution tree is selected. Old snapshots
are accepted as source identities only when their exact module/hash matches
an explicit public regeneration inventory. An older canonical plan cannot
stand in for changed final consumers.

The default output is an inspection manifest. Missing final sources/plans or a
missing final reviewed commit produce INCOMPLETE_SOURCE_SELECTION_NO_FINAL_BUNDLE_ACCEPTANCE.
Final archive selection requires the exact reviewed HEAD and all selected bytes
to match that commit:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/select_source_bundle.py \
  --context /path/to/pinned-context.json --out /fresh/final-source-selection \
  --proof-plan FAMILY=/path/to/current/PLAN.json \
  --reviewed-commit EXACT_FINAL_COMMIT --require-complete
~~~

Repeat every family argument from the first example. --require-complete fails
on any unresolved obligation. A plan, a partial manifest, or successful source
hashing is not a final bundle acceptance, proof receipt, or official Comparator
receipt. Root must rerun selection after final source/registration changes.

The optional normal Python CLI imports PyYAML (retained interpreter observation:
6.0.3). The finite proof gate compiles isolated Solution/Challenge entry modules
directly with Lean and does not invoke that Python CLI; this observation does
not add a Python package dependency to those proof routes.

The retained normal CLI checks are fingerprint, fingerprint --check,
check-graph, check-closure, check-pins, and gen-challenges --check. The source
selection preserves scripts/verify-comparator.sh because check-pins skips its
work when that script is absent. No official Comparator execution is implied.
The tested full scaffold environment can be created separately with:

~~~bash
python3.11 -m venv /fresh/cli-venv
/fresh/cli-venv/bin/python -m pip install \
  PyYAML==6.0.3 ruamel.yaml==0.18.16 ruamel.yaml.clib==0.2.15
~~~

Only PyYAML is needed by the listed checks; ruamel supports node editing and
comment-preserving metadata changes. This is a documented recipe, not an
installation or fresh normal-CLI run performed by the source selector.

The immutable primary payload `fixed_width-B_named-r1/check.py` is historical
model-submission evidence and contains `assert`; it is not an active
acceptance validator. Reproduction uses the separate199-module compiler and
independent type/axiom/dependency audits. The original payload bytes are never
modified to make modern validators pass, and ordinary Python certificate
checking is not labeled source-first PV.
