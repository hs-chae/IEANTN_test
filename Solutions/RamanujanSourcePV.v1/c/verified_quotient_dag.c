/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
/* Source-first migration in progress. Its full source refinement is pending;
   successful execution of this file is not by itself a Lean proof. */
#include <stdint.h>

/* Flat seven-word records: p, v, value, a, b, c, d. All references point to
   an already accepted record. Pointers own exactly7*count readable words. */
uint64_t rpc_check_quotient_dag(const uint64_t *rows, uint64_t count) {
    if (count > UINT64_MAX / 7) return 0;
    for (uint64_t i = 0; i < count; ++i) {
        const uint64_t *r = rows + 7 * i;
        uint64_t p = r[0], v = r[1], value = r[2];
        if (p == 2) {
            if (value != (v < 2 ? 0 : v - 1)) return 0;
        } else {
            if (p < 3) return 0;
            uint64_t q = p - 1;
            if (q > UINT64_MAX / q) return 0;
            if (r[3] >= i || r[4] >= i || r[5] >= i || r[6] >= i) return 0;
            const uint64_t *a = rows + 7 * r[3];
            const uint64_t *b = rows + 7 * r[4];
            const uint64_t *c = rows + 7 * r[5];
            const uint64_t *d = rows + 7 * r[6];
            if (a[0] != q || a[1] != v || b[0] != q || b[1] != q ||
                c[0] != q || c[1] != q - 1 || d[0] != q || d[1] != v / q) return 0;
            if (b[2] == c[2] || v < q * q) {
                if (value != a[2]) return 0;
            } else {
                if (d[2] < c[2] || a[2] < d[2] - c[2]) return 0;
                if (value != a[2] - (d[2] - c[2])) return 0;
            }
        }
    }
    return 1;
}
