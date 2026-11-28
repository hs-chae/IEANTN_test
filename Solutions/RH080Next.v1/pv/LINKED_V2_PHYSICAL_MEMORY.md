# Associated final consumers with a separate physical-memory boundary

`compile_verified_batch_linked_v2.py` and `reproduce_w4_main_v2.py` are additive
resource-only versions. The old tools and their historical evidence stay
unchanged. No Lean mathematical source or statement is changed.

Both CLIs require `--worker-virtual-as unlimited` and `--memory-gib 300`.
The latter declares the independent physical policy; it is not a virtual AS cap.
Before compilation, the helper requires its actual owned cgroup to have
memory.max300GiB and memory.swap.max0. The outer existing resource supervisor
must enforce the separate1TiB RAM/disk admission and host/scratch reserves.
Actual compiler invocations explicitly use `prlimit --as=unlimited`, avoiding
premature failure from large virtual mappings while preserving the physical cap.

All previous context/compiler/source/object/receipt checks, strict JSON parsing,
immutable hardlinks, root freshness and actual compiler result checks remain.
Plan and result record null per_compiler_AS_bytes and the policy
EXPLICIT_RLIM_INFINITY_WITH_SEPARATE_PHYSICAL_CGROUP. This is a source-associated
consumer build; it does not relabel inherited modules as freshly source-cold or
claim whole source-first PV merely because compilation succeeds.

The W4 wrapper still requires all six actual final modules to compile and the
complete source/main/norm/prime proof-value, exact-type, matched-control and
standard-axiom marker. Bounded tests of a cheap independent audit root do not
replace this final six-module gate. Compiler/runtime/OS/hardware contracts remain
explicit trust boundaries.

```sh
python3 Solutions/RH080Next.v1/pv/reproduce_w4_main_v2.py \
  --context /pinned/context.json \
  --bank /accepted/N24-format-bank --bank /accepted/norm-transfer-bank \
  --bank /accepted/finite-main-bank --bank /accepted/population-format-bank \
  --bank /accepted/population-algebra-bank \
  --run /fresh/final-W4-consumers --memory-gib 300 --worker-virtual-as unlimited
```

An invalid physical policy,
unowned cgroup, missing virtual-AS flag or numeric replacement for `unlimited`
rejects without a final acceptance. No alternate weaker mathematical branch is
substituted if the final proof fails.
