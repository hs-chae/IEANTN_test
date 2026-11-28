# Bounded v4 resource-guard controls

These tests check the resource guard's command-line deadline range and actual
child timeout handling. They make no mathematical or source-first PV claim.
The supported deadline is 1 through 7200 seconds; the default remains 1200.
The existing bounded owned-process/paused-scan mechanism is unchanged.

From the repository root, use Python 3 on Linux with pidfd support and a working
user systemd service manager. The timeout test requires its own cgroup with
memory.max = 322122547200 bytes (300 GiB) and memory.swap.max = 0. Each guard
invocation checks genuinely available RAM and independent free disk of at least
1 TiB, keeps its existing host reserve, and checks its tiny owned scratch root.
An admission failure is not a passed timeout test. Do not run these commands
inside a shared service containing unrelated work.

```sh
qrh_guard_project="$PWD/Solutions/RH080Next.v1"
qrh_guard_repro=$(mktemp -d)
PYTHONDONTWRITEBYTECODE=1 python3   "$qrh_guard_project/reproduction/test_bootstrap_guard_v4_cli_boundaries.py"   --source "$qrh_guard_project/reproduction/bootstrap_quiescent_resource_guard_v4.py"   --out "$qrh_guard_repro/parser-controls"
systemd-run --user --wait --collect   --unit="qrh-guard-v4-controls-$$"   --property=MemoryMax=322122547200 --property=MemorySwapMax=0   --property=OOMPolicy=continue --setenv=PYTHONDONTWRITEBYTECODE=1   /usr/bin/python3 "$qrh_guard_project/pv/generic_page_policy_exec.py"   --disable-thp --receipt "$qrh_guard_repro/PAGE_POLICY.json" --   /usr/bin/python3 "$qrh_guard_project/reproduction/test_bootstrap_quiescent_guard_v4.py"   --source "$qrh_guard_project/reproduction/bootstrap_quiescent_resource_guard_v4.py"   --out "$qrh_guard_repro/timeout-controls"
```

Use fresh output directories. The parser test rejects five inputs in each of
normal, -O and -OO modes, without launching a child. The timeout test runs six
short successful children (default and maximum deadline in each mode) and
three actual 1-second timeout cases; each timeout child initially sleeps 20 seconds
and must be stopped by the guard. Check both final RESULT.json files and the
nine individual RESOURCE.json receipts. This test is not a 7200-second workload.

The guard imports the pinned original pv/supervise_resource_run.py helper;
the reproduction receipt lists that exact existing runtime source, the v4
guard and generic_page_policy_exec.py hashes. These project sources must be
present together; this test is not a standalone copy of a single guard file.

## Preserved actual evidence

- actual-timeout-success-v2 contains the completed six positive and three actual
  timeout controls in all three Python modes. Its original RESULT SHA-256 is
  84040134fd38337f17ab4a6f485718a808e34f8ab8d793852d2e09bd0f19465b.
- actual-cli-boundaries-v1 contains the original 15 parser/range rejections.
  Its RESULT SHA-256 is
  3e3beba2c210084c609458bab5011e11e42b85e55fce515e1f1828b92cc607ef.
- actual-timeout-admission-failure-v1 preserves the first actual attempt's
  RAM/disk/campaign admission rejection. There was no RESOURCE or RESULT
  receipt for that case. It is not counted among the completed controls.

Historical command arrays retain their actual execution paths. Use the clean
commands above for a new checkout. The timeout controller is published with
identical bytes under its descriptive public filename. The CLI-boundary
controller changes only --source/--out path selection; its executed original
is preserved under historical-executed. No historical receipt was rewritten,
and no fresh full mathematical/program run is claimed by this package.

The portable CLI controller was also actually run against the exact public v4
guard: actual-portable-cli-boundaries-v1 preserves its 15 successful rejections
across normal, -O and -OO. PORTABLE_BOUNDARY_EXECUTION_IDENTITY_v1.json pins
the executed adapter source, guard source, command and original RESULT. This
additional small run launched no child and repeated no timeout, renaming,
compiler or mathematical workload.
