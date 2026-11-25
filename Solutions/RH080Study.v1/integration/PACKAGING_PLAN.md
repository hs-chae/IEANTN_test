# Ordinary Lake packaging

The accepted source-only replay manifests remain the mathematical verification
records. This additional packaging step makes the new canonical solution
projects build with ordinary Lake as well.

Register the existing helper modules, without changing their mathematical
source, in one local `RH080Study` package. Group libraries by their existing
source directories; reuse the pinned previous-study generic interval/Fourier
sources. Each new solution depends on this provider package and the unchanged
IEANTN core. Do not register replay-only module aliases or audit modules as
mathematical providers. The public manifest records every registered source
and its SHA-256, so registration can be regenerated from a clean checkout.

Build dependency metadata before compiling. Preserve failed attempts and
distinguish ordinary Lake builds from the separate source-only proof replays.
The large C execution proof receives its justified 256 GiB address-space limit
and runs alone; other numerical compilations use the recorded smaller limits.
Do not copy application objects into a Lake build or manufacture build traces.
