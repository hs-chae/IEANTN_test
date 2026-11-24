# Actual bounded clean-source run

The first real execution of the physical-aware clean recipe passed on
2026-11-24. It regenerated and proved `Nat.primeCounting 1000 = 168`, compiled
60 application/audit modules from source using only the pinned generic libraries,
and compiled the original high-input C source/model and independent source grammar.
The parameterized high-source output theorem still takes its exact numerical
count as an argument. This small run does not prove the fixed high-input output.

The accepted outer result has SHA256
`dbd7bf6bb909f4b4f4c6c1f89aba8123fa365fcba62ef16f7b85cdca93de1da6`.
The complete source compilation took 1,266.685 seconds. Its measured maximum
child RSS was 32,378,490,880 bytes; compiler-tree RSS sampled once per second
reached 32,379,613,184 bytes. The engine reported 60,701,558 bytes of replay
files and zero observed owned OOM events. The entire small-run directory used
64,331,776 allocated bytes at the subsequent readback. Each compiler had a
48 GiB virtual-address ceiling, independently of its observed physical RAM.
The only allowed mathematical axioms were `propext`, `Classical.choice` and
`Quot.sound`; numerical arithmetic, gap, entry and root facts had empty axiom
lists. No native execution axiom was admitted.

The actual command is preserved in the run's plan and launch receipt:

```sh
python3 portable-source-run/reproduce.py --context /actual/generic/GENERIC_CONTEXT.json \
  --out /fresh/owned/portable-source-smoke-v1 --smoke --jobs 1 --cpus 64
```

The separate completed-reader control receipt has SHA256
`7a727cf2ed20765ecd2d7f13150e7b48d3c296275fac15e7e00bfdb30e707b2b`.
All 51 decisions passed: one actual positive public-CLI readback and sixteen
negative public-CLI fixture cases in each of normal, `-O` and `-OO` modes.
The negative cases inject finite, read-only file-byte views in fresh CLI
processes; they never modify the accepted artifacts and are not new executed
proof runs. They cover strict JSON/counter types, omitted source, changed
commands, an external byte-identical object, source stability, real GNU-time
duration, omitted/empty dependencies and relabelling the small run as a
completed high-output proof. Reproduce these controls with:

```sh
python3 portable-source-run/test_completed_readback.py \
  --actual /actual/completed/small-run --out /fresh/owned/reader-controls
```

`make_source_packet.py` copies the exact explicitly enumerated source recipe,
including its Python import dependencies. Its first packet contained 121 files,
1,691,002 bytes, no application proof objects and no generated numerical inputs.
An optional relocated small proof run was interrupted by an intentional
`SIGUSR1` resource drain after two modules. The launch used an overly simple
estimate of other jobs' potential growth; the measured process forest required
more reserve. Its stopped receipt is retained as an incomplete control, with no
accepted result. The already accepted first small run was untouched. Complete
relocation proof acceptance therefore remains pending until safe measured
headroom is available.

The full fixed target and scientific sources remain unchanged. The single new
fast full-source recipe is available, but no second full high-count campaign
has been executed by this smoke study. The actual fixed high result requires
the separate exhaustive arithmetic completion, cold data/gap complement,
unchanged final theorem and source-indexed final consumer. These are distinct
receipts and must not be inferred from this small workflow control.
