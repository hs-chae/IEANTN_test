# Strict diagnostic build

From this directory, build both O0 and O2 using:

    gcc -O2 -std=c17 -fno-fast-math -fno-associative-math -ffp-contract=off \
      -fexcess-precision=standard -frounding-math -msse2 -mfpmath=sse \
      -Wall -Wextra -Werror fks2_table4_transport.c harness.c -lm -o transport
    ./transport

The harness checks binary64 format and round-to-nearest. The expected exact
output bits are3cc0fd404ee3d945; displayed decimal4.7154676038087135e-16. These
runs are diagnostics and do not replace modeled execution and its Lean proof.

The30array entries and suffix constants are exact terminating decimal spellings
of dyadic binary64 values; Lean checks their parsing/loaded values, upward
analytic relation and normal range. No external transcendental library is used
at runtime. The scale is exactly2^-58. Input and operation ledgers are in the
portable evidence bundle.
