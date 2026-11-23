# Optional historical resource23 provenance guard

Actual controller: reproduce_integration.py, SHA9b630a9fec993749d6fefdf81dd7893cac2b4f674392be21eb385c1fecd106e6.
The optional branch currently binds RESULT/BUILD and checks each row's integer
return code and object hash. It does not compare the stored source/log bytes.

Under the fixed approved S, the actual --check CLI accepts altered
resources/source/RamanujanPV/FiniteLogSource.lean and
resources/logs/RamanujanPV.FiniteLogSource.stdout in all three Python modes.
BUILD and RESULT metadata remain byte-identical in these cases. This leaves the
same valid original kernel object in use; mathematical conclusions are unchanged.
The resource-complete clean261 route does not use this optional historical branch.

A minimal guard can reuse the existing fixed pi/RESOURCE_CLOSURE.json, confirm
its23 rows equal base261.modules[238:], and bind its hash to the existing
resource RESULT.source_manifest_sha256. For each zipped fixed/BUILD row, check:
module identity/order; strict integer returncode0; current fixed source SHA equals
manifest/BUILD/stored source SHA; object SHA; stdout/stderr SHA; and printed axiom
audits. Bind resource/reproduce.executed.py to RESULT.controller_sha256 (and the
approved controller version), retaining the existing RESULT/BUILD/basis joins.
Check the actual C include at resource/source/c/verified_finite_log.c against
fixed pi/RESOURCES.json, which is already bound by resource_manifest_sha256.
No new mathematical statement, executable algorithm or verification architecture
is needed. A revised-controller supplemental24 replay should be labeled as such,
while retaining historical controller/run evidence.
