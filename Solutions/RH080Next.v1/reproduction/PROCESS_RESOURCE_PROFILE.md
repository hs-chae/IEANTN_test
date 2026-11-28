# Reproduce the posthoc process resource profile

The current continuation uses a process-only transparent-huge-page policy
before the coordinator starts. It preserves every numerical C source,
mathematical checker, fixed input, parameter, theorem statement and successful
proof prefix. It is a separate resource profile, not a new mathematical
algorithm, source-first PV result or change to the original experiment score.

The exact utility and documented generic Linux contract are
`../pv/generic_page_policy_exec.py` and `../pv/GENERIC_PAGE_POLICY.md`.
The utility sets `PR_SET_THP_DISABLE(1)`, checks `PR_GET_THP_DISABLE == 1`
and its own `THP_enabled == 0`, writes a fresh pre-exec observation and then
executes an absolute executable. The process policy is inherited through
fork/exec. It changes neither host-global controls nor another existing
process. A policy receipt establishes the pre-exec observation only; child
execution, source/model correctness and the mathematical result still need
their own verification receipts.

## Keep all new storage under one owned campaign directory

Use one experiment-owned directory such as `/owned/rh080-reproduction` for
bootstrap dependencies, regenerated data, proof outputs and resource receipts.
Use a different fresh subdirectory for each run. Preserve the source checkout
and original research artifacts outside disposable output directories.

The existing outer resource supervisor must scan that whole campaign root,
not only a proof stage's output. This makes its total scratch accounting
include bootstrap caches as well as numerical/proof artifacts. Its physical
limit remains 300GiB with no swap. It independently checks available RAM and
free disk against 1TiB admission, preserves 256GiB host RAM, admits scratch
below 270GiB and stops below the 300GiB allowance at its 290GiB guard. Unlimited
virtual address space is not additional physical RAM. The inner pipeline's
per-stage checks remain in effect.

## Apply the policy before bootstrap context/version checks

Here is the process wrapper for a fresh bootstrap. All executable paths must
be absolute. The receipt directory must already exist and its file must be
fresh. The dependency workspace and context output must be fresh as required
by the bootstrap parser.

```sh
/absolute/python3 /absolute/repository/Solutions/RH080Next.v1/pv/generic_page_policy_exec.py \
  --disable-thp --receipt /owned/rh080-reproduction/bootstrap-policy.json -- \
  /absolute/python3 /absolute/repository/Solutions/RH080Next.v1/reproduction/bootstrap_context.py \
  --fetch --workspace /owned/rh080-reproduction/dependencies \
  --compiler /absolute/pinned/lean \
  --output /owned/rh080-reproduction/context.json
```

Run this command inside its separately admitted owned 300GiB/no-swap service
when doing a real fetch, with the same campaign-wide outer supervisor recipe
below. A successful fetch has its own context/bootstrap receipt. A plan,
help output or pre-exec policy observation is not a successful fetch.

## Wrap the whole proof pipeline, not only a final Lean child

Construct an explicit outer-supervisor command manifest. For example, the
following Python snippet prepares the unchanged driver command and exact
execution-source pins. Edit the three absolute paths before using it.

```python
from pathlib import Path
import hashlib,json
repo=Path('/absolute/repository')
campaign=Path('/owned/rh080-reproduction')
python=Path('/absolute/python3')
project=repo/'Solutions/RH080Next.v1'
driver=project/'reproduction/reproduce_all.py'
supervisor=project/'pv/supervise_resource_run.py'
policy=project/'pv/generic_page_policy_exec.py'
command=[str(python),str(driver),'--context',str(campaign/'context.json'),
         '--run',str(campaign/'full-run'),'--execute',
         '--unit','rh080-clean-full.service']
manifest={'command':command,'source_pins':[
    {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    for p in [driver,supervisor,policy]]}
(campaign/'full-command.json').write_text(json.dumps(manifest,indent=2)+'\n')
```

Then launch the owned service with the policy outside its resource supervisor:

```sh
systemd-run --user --unit rh080-clean-full \
  --property=MemoryMax=300G --property=MemoryHigh=270G \
  --property=MemorySwapMax=0 --property=TasksMax=512 \
  /usr/bin/taskset --cpu-list 96-99 \
  /absolute/python3 /absolute/repository/Solutions/RH080Next.v1/pv/generic_page_policy_exec.py \
  --disable-thp --receipt /owned/rh080-reproduction/full-policy.json -- \
  /absolute/python3 /absolute/repository/Solutions/RH080Next.v1/pv/supervise_resource_run.py \
  --root /owned/rh080-reproduction \
  --command /owned/rh080-reproduction/full-command.json \
  --receipt /owned/rh080-reproduction/full-supervisor.json \
  --live /owned/rh080-reproduction/full-live.json
```

The CPU list 96--99 is the actual ordinary-worker placement of this recorded
profile, not a claim about another machine's allowed CPUs. Confirm that those
CPUs are available on the reproduction host, or record another explicitly
chosen valid list. Record the actual affinity from the policy receipt rather
than inferring it from a requested service property. The earlier service
requested 64--79 but observed 0--127; that request is not reported as measured
pinning. The source-cold checker keeps its original worker count and exact
arithmetic regardless of placement.

Use the same outer arrangement for the bootstrap command by placing its
argument vector in a different fresh command manifest and using fresh
supervisor/policy output paths. All dependencies and outputs stay under the
same owned campaign root so disk space is counted separately from RAM.

## Preserve unsuccessful profiles and distinguish observations

The earlier source-identical Final run was intentionally stopped after
71min42s during a sustained memory-management stall. Its measured user CPU
was 1567.32s, system CPU 2734.28s, maximum RSS 179939860KiB and completed owned
OOM count 0. No Final object or accepted proof was produced; receipt exit 143
records the intentional stop. The earlier virtual-AS 256GiB allocation panic
is another distinct resource failure. Neither is a mathematical counterexample.

The memory-stall/PSI observations and predominantly system CPU are measured.
A THP/compaction explanation is an operational hypothesis, not a per-task
stack-trace diagnosis; machine-wide compaction counters include unrelated
work. The GNU-time log printed `Exit status: 0` after signal15, but the actual
controller receipt records143, no Final object and no acceptance. That time
field must not be used to infer a successful proof.

A tiny unchanged helper completed in 0.356s under the new process policy;
the prior live-state observation spent about 70s in system CPU. These are
observations under different live host conditions, not a causal speedup
claim. Likewise a separate proof-only S13 variant passed 18 Std3 roots but
took 330s versus 309s in its bounded comparison; it was not used to replace
the source-identical production checker. Final numerical/ANT acceptance
must be read from the actual completed worker, independent gate and final
consumer receipts.

The generic Python/libc/Linux process-interface, compiler, runtime and hardware
contracts remain trusted. No host setting, compiler correctness, application
success or mathematical truth is inferred merely from this resource utility.
