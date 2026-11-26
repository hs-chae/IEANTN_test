# Original Fap norm provider

This Solution proves the unchanged0.7817960157900848 cap for the actual original400-node Fap affine Fourier witness, conditional on `BRFourierInput.v1.norm_identity`. It consumes a complete131072-point exact integer FFT trace, its true DFT error bound and global chord quadrature. This is kernel-only numerical verification; the actual C FFT source-to-ANT path remains incomplete.

Before `lake build`, run `python ../RH080Next.v1/primal/finite/prepare_fap_library.py` from this directory, and ensure the parent RH080Next library registration is integrated. See `../RH080Next.v1/primal/finite/README.md` for the clean full reproduction pipeline, exact hashes and trust boundary. `comparator.json` is configuration, not an accepted Comparator receipt.
