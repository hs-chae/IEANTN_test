# Continue the original fresh source replay with measured resource profiles

`resume_profiled_source_closure.py` continues an interrupted, originally fresh
application build. It accepts only successful objects from that SAME run, after
checking every source, compiler command, source snapshot, object, stdout, stderr
and peak-RAM receipt against the immutable original plan. It preserves failed
and interrupted attempts. It never resets the cold-build clock or imports an
unrelated application cache.

The recorded467-module run had185 original successes and226 successes in its
first continuation. A clean scheduled drain finished411 modules, left56 pending,
and stopped with no running workers. Only the controller received SIGUSR1;
no compiler worker was killed. The next additive controller retains that entire
accepted population and uses these prospective address-space ceilings:

| Module | GiB |
|---|---:|
| DemandCriticalPair.Check0000 |96|
| DemandCriticalPair.Check0250 |96|
| DemandCriticalPair.GapCheck |192|
| Other modules |48|
| Sum of active worker allowances |at most300|
| RAM retained for the host |at least512|

Successful old48GiB receipts are preserved as their original results; they are
not rerun or relabelled as96/192GiB runs. A heavy ready module can delay further
dispatch until existing workers finish. Each actual dispatch and release is
journalled, and the process's inherited soft/hard address-space limits are
observed separately from actual peak resident RAM.

For an unfinished original run whose source paths and PLAN.json remain intact:

```bash
python3 scripts/resume_profiled_source_closure.py \
  --run-root ORIGINAL_FRESH_RUN --out ORIGINAL_FRESH_RUN/resume-profiled-v1 \
  --jobs 4 --cpus 8,9,10,11 --memory-gib 48 \
  --profile-json evidence/COLD467_RESOURCE_PROFILE.json \
  --aggregate-gib 300 --host-reserve-gib 512
```

The output must be fresh and inside the original run. Add `--readback-only`
with a DIFFERENT fresh output directory to inspect every existing accepted
artifact and preview unaccepted objects without dispatching Lean or moving any
object. This reports `READBACK_ONLY_NOT_REPLAYED`. For execution, only
unaccepted objects inside the experiment's original object bank are moved to a
preserved quarantine; accepted objects and unrelated workspaces are unchanged.

The controller needs genuinely1TiB available RAM for this high-resource policy.
It checks actual available memory before launch, checks the512GiB reserve when
dispatching, and reserves each worker's complete allowance before submission.
Disk availability is a separate capacity. An address-space allocation panic is
recorded separately from SIGKILL/OOM evidence; SIGKILL alone is not proof that
the OS OOM killer acted.

After every original module and the mandatory final theorem/axiom audit passes,
the controller writes a pending candidate, checks all original and new artifact
hashes and the complete reservation journal, then atomically publishes RESULT.
Independently reread it with:

```bash
python3 scripts/resume_profiled_source_closure.py \
  --check ORIGINAL_FRESH_RUN/resume-profiled-v1
```

The actual normal/-O/-OO CLI controls are reproducible with:

```bash
python3 scripts/test_profiled_resume_cli.py FRESH_CONTROL_DIRECTORY
```

These21 routes include real Lean compilation and reused prerequisites, measured
192/96/48GiB process ceilings,288GiB simultaneous reservations under the300GiB
limit, final readback, and rejection of over-limit policies, changed prior
artifacts and a changed journal. They are explicitly synthetic controller
fixtures, not new research outcomes. The current source and receipts are in
`evidence/profiled467-continuation-controls-v1/PACKET.json`.

This467-module stage targets the original segment checker, critical counts and
1,001-wide consumer. It is not a complete cold replay of the later million-wide
scalar programs or the1,755,663-row source-scalar certificate. The latter's full
prime-count witnesses are still a separate open obligation. Check the actual
final RESULT; a launch/readback packet is not proof of completed execution.
