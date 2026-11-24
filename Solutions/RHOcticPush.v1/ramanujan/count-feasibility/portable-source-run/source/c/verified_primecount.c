/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
#include <stdint.h>

uint64_t rpc_is_prime(uint64_t n) {
    if (n < 2) return 0;
    for (uint64_t d = 2; d <= n / d; ++d) {
        if (n % d == 0) return 0;
    }
    return 1;
}

uint64_t rpc_count(uint64_t bound) {
    uint64_t n = 0;
    uint64_t count = 0;
    while (n < bound) {
        ++n;
        count = count + rpc_is_prime(n);
    }
    return count;
}
