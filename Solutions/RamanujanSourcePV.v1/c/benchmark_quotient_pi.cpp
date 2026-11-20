/* Copyright (c) 2026 hschae. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: hschae and Codex
 */
// UNTRUSTED NUMERICAL GENERATOR / BENCHMARK. No formal verification claim.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

int main(int argc, char **argv) {
  try {
    if (argc != 2) throw std::runtime_error("usage: benchmark_quotient_pi N");
    std::size_t used = 0;
    std::uint64_t n = std::stoull(argv[1], &used);
    if (used != std::string(argv[1]).size() || n > 2000000000000ULL)
      throw std::runtime_error("N must be an integer in [0,2000000000000]");
    const auto start = std::chrono::steady_clock::now();
    if (n < 2) {
      std::cout << "{\"N\":" << n << ",\"pi\":0,\"untrusted_generator\":true}\n";
      return 0;
    }
    auto r = static_cast<std::uint64_t>(std::sqrt(static_cast<long double>(n)));
    while (static_cast<__uint128_t>(r + 1) * (r + 1) <= n) ++r;
    while (static_cast<__uint128_t>(r) * r > n) --r;
    std::vector<std::uint64_t> small(r + 1), large(r + 1);
    for (std::uint64_t i = 1; i <= r; ++i) {
      small[i] = i - 1;
      large[i] = n / i - 1;
    }
    std::uint64_t updates = 0, primes = 0;
    for (std::uint64_t p = 2; p <= r; ++p) {
      if (small[p] == small[p - 1]) continue;
      ++primes;
      const std::uint64_t before = small[p - 1];
      const std::uint64_t stop = std::min(r, n / (p * p));
      for (std::uint64_t i = 1; i <= stop; ++i) {
        const std::uint64_t ip = i * p;
        const std::uint64_t sub = ip <= r ? large[ip] : small[n / ip];
        if (sub < before || large[i] < sub - before)
          throw std::runtime_error("unsigned subtraction invariant failed");
        large[i] -= sub - before;
        ++updates;
      }
      const std::uint64_t square = p * p;
      if (square <= r) {
        for (std::uint64_t v = r; v >= square; --v) {
          const std::uint64_t sub = small[v / p];
          if (sub < before || small[v] < sub - before)
            throw std::runtime_error("small-table subtraction invariant failed");
          small[v] -= sub - before;
          ++updates;
        }
      }
    }
    const double seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - start).count();
    std::cout << "{\"N\":" << n << ",\"pi\":" << large[1]
              << ",\"sqrt\":" << r << ",\"primes_through_sqrt\":" << primes
              << ",\"table_updates\":" << updates
              << ",\"table_bytes\":" << 16 * (r + 1)
              << ",\"seconds\":" << seconds
              << ",\"untrusted_generator\":true}\n";
  } catch (const std::exception &error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
