# Integration execution corrections

- The first bounded packaging-only interrupt used systemd’s newer option
  spelling `--kill-whom=all`. This host rejected it before sending a signal.
  Retried with its supported `--kill-who=all` spelling after rechecking the
  exact packaging unit identity. No other unit was targeted.

- The new packaging preflight assumed the user-service cgroup exposed
  `cpu.max`. This host delegates memory but not that CPU controller, so the
  guard rejected before creating a run or starting Lake. Preserved the exact
  failed controller/launch. Corrected the observation: record unavailable
  quota explicitly and enforce the independently real16-CPU affinity bound;
  retain the strict300GiB memory/swap0 and host-reserve guards. No mathematical
  source or accepted proof artifact changed.
  The same preflight inspection confirmed this kernel also lacks `memory.peak`;
  the controller now records that absence and the actual0.5-second memory/RSS
  samples, without calling the sampled maximum an exact peak.

- The actual full repository check found a central-provider packaging omission:
  RH080Study lacked its own `lean-toolchain`, producing one new error beyond
  the inherited49. Added the exact repository pin. The active expensive Lake
  run keeps its frozen controller; after it finishes, registration will include
  this file and a further genuine all10 incremental pass will verify the final
  packaging state. The50-error check remains preserved. No math source changed.
