# Process-only page policy before a verified computation

`generic_page_policy_exec.py --disable-thp --receipt /fresh/policy.json -- /absolute/executable ARGS...`
sets and verifies a resource policy for its own process, then executes that argv.
The policy is inherited through fork and exec. It never writes global THP controls
or changes another existing process. The resource receipt explicitly precedes
execution: it records verified policy, not child success or mathematical proof.
The actual compiler/program and final proof still require their ordinary receipts
and audits.

The Linux kernel's [process THP controls](https://docs.kernel.org/admin-guide/mm/transhuge.html#process-thp-controls)
specify the process-only `PR_SET_THP_DISABLE`/`PR_GET_THP_DISABLE` interface and
fork/exec inheritance. The wrapper checks the installed Linux UAPI constants41/42,
sets value1, requires GET1, and requires its own `/proc/self/status` THP_enabled0
before publishing a fresh atomic pre-exec observation. This contract was tested
on kernel5.15.0-186-generic. Local headers, wrapper source and execution parameters
are hashed in the evidence.

Place this wrapper outside the resource supervisor so context/version checks
also inherit the policy. For example, the owned unit can execute:

```sh
/usr/bin/taskset --cpu-list 96-99 python3 generic_page_policy_exec.py \
  --disable-thp --receipt /fresh/process-page-policy.json -- \
  /absolute/python3 supervise_resource_run.py \
  --root /owned/campaign --command /fresh/unchanged-child-command.json \
  --receipt /fresh/supervisor.json --live /fresh/live.json
```

The actual unit still needs its independently checked physical RAM/no-swap limit,
separate RAM/disk admission, host reserve and campaign scratch guard. A page policy
or CPU placement is not additional physical RAM. Preserve the original numerical
source, algorithm, parameters and mathematical statement. Record this as a new
posthoc resource profile; do not rewrite original failures or experimental scores.
The supervisor's child command can remain unchanged, with the outer policy source
and receipt recorded separately.

An actual unchanged tiny Lean helper completed in0.356s with GET1 and observed
compiler THP_enabled0. It had previously taken70.96s, of which70.76s was system CPU,
under a different live resource state. These observations motivated the resource
change; they are not a causal performance theorem. Global compaction counters
also include unrelated concurrent work and are not uniquely attributable.

Normal Python, `-O` and `-OO` controls verified actual exec inheritance and
rejected18 invalid CLI/receipt cases. Source-first PV is not claimed for this
resource wrapper. Generic Python/libc/Linux syscall, compiler, runtime and
hardware contracts remain trusted; application mathematical correctness must
continue to be proved by the separate source/model/ANT chain.
