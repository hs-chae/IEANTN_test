# QRH propagation proofs

Run `lake build PropagationSolution MaximumReplay DensityReplay TableReplay` here,
using the repository's Lean4.34.0-rc2 toolchain and committed dependency pins.

`PropagationSolution` proves all seven exact generated challenges. `MaximumReplay`
composes the arithmetic and zero-geometry routes from the original named source
premises plus QRH. It imports the existing integration, prime-interval,
Dudek--Platt and FKS2 proof implementations. `DensityReplay` also imports the
checked CH2.v6 numerical certificates, retaining the corrected FKS density and
finite-height RH premises explicitly. No new analytic transfer is assumed.

`HasPowerLogBound` is shared vocabulary. The general moving-envelope and
partial-summation interfaces are in `PowerBounds` and `PiPower`; concrete
log-free consequences are in `DensityApplications`. `TableReplay` proves one
uniform update for the 46 eligible rows of the unchanged BKLNW table.

The small alias modules are relative symlinks to the existing proof sources;
they avoid collisions between packages exporting a module named Solution.
The unique MaximumReplay name similarly avoids the existing QRHCH2 Replay module.

Local checks are author evidence. Official Comparator receipts are created only
by the repository's approved verification workflow; no receipt is supplied here.
OpenAI's published proof uses a different compiler and is replayed separately.
