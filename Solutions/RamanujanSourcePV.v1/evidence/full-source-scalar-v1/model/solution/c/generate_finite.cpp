/* Copyright (c) 2026 hschae. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: hschae and Codex
 */
// UNTRUSTED certificate generator. No formal-verification claim.
// Integer arithmetic for every certificate predicate; external prime libraries
// are untrusted until a sound source-first consumer closes their outputs.
#include <primecount.hpp>
#include <primesieve/iterator.hpp>
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
using U = std::uint64_t;
using W = __uint128_t;
constexpr U F = U{1} << 60;
constexpr U SCALE = U{1} << 20;
U narrow(W x) { if (x > std::numeric_limits<U>::max()) throw std::runtime_error("uint64 range"); return static_cast<U>(x); }
U ceildiv(W a, W b) { if (!b) throw std::runtime_error("zero division"); return narrow(a / b + (a % b != 0)); }
U log_series_upper(U num, U den) {
  const U z = ceildiv(W{F} * num, den);
  const U z2 = ceildiv(W{z} * z, F);
  U power = z;
  W sum = 0;
  for (U k = 0; k < 20; ++k) {
    sum += ceildiv(power, 2 * k + 1);
    power = ceildiv(W{power} * z2, F);
  }
  return narrow(2 * sum + ceildiv(W{2} * power * F, W{41} * (F - z2)));
}
U log_upper(U n) {
  if (n < 2) throw std::runtime_error("log domain");
  U two = 1, k = 0;
  while (two <= n / 2) { two *= 2; ++k; }
  static const U log2 = log_series_upper(1, 3);
  return ceildiv(W{k} * log2 + log_series_upper(n - two, n + two), SCALE);
}
U e_lower() { U term = F, total = F; for (U k = 1; k <= 20; ++k) { term /= k; total += term; } return total; }
U sqrt_floor(W n) {
  U r = static_cast<U>(std::sqrt(static_cast<long double>(n)));
  while (W{r + 1} * (r + 1) <= n) ++r;
  while (W{r} * r > n) --r;
  return r;
}
U parse(const char *s) { std::size_t pos = 0; U n = std::stoull(s, &pos); if (pos != std::string(s).size()) throw std::runtime_error("invalid integer"); return n; }
void word(std::ofstream &out, U x) { for (unsigned i = 0; i < 8; ++i) out.put(static_cast<char>((x >> (8 * i)) & 255)); }
int main(int argc, char **argv) {
 try {
  if (argc != 5) throw std::runtime_error("usage: generate_finite BEGIN END_EXCLUSIVE CERT.bin actual|unit");
  U n = parse(argv[1]); const U begin = n, end = parse(argv[2]);
  if (n < 38358837683ULL || n >= end || end > 1620000000001ULL) throw std::runtime_error("range");
  const std::string mode = argv[4];
  if (mode != "actual" && mode != "unit") throw std::runtime_error("mode");
  primecount::set_num_threads(1);
  const auto start = std::chrono::steady_clock::now();
  const U elo = e_lower(), ehi = elo + 22;
  U j = narrow(W{n} * F / ehi);
  U pcount = static_cast<U>(primecount::pi(static_cast<std::int64_t>(n - 1)));
  U qcount = static_cast<U>(primecount::pi(static_cast<std::int64_t>(j)));
  const U initialP = pcount, initialQ = qcount;
  primesieve::iterator pi(n, end), qi(j + 1, narrow(W{end} * F / ehi) + 1);
  U p = pi.next_prime(), q = qi.next_prime();
  std::ofstream out(argv[3], std::ios::binary | std::ios::trunc);
  if (!out) throw std::runtime_error("certificate open");
  U cells = 0, p_events = 0, q_events = 0, min_width = std::numeric_limits<U>::max(), max_width = 0;
  W min_gap = ~W{0};
  while (n < end) {
    j = narrow(W{n} * F / ehi);
    while (q <= j) { ++qcount; ++q_events; q = qi.next_prime(); }
    const U lu = log_upper(n), a = narrow(W{n} * elo / lu);
    if (!qcount || W{a} * qcount == 0) throw std::runtime_error("empty RHS");
    const U allowed = sqrt_floor((W{a} * qcount - 1) / SCALE);
    U next;
    if (mode == "actual") {
      while (p < end && pcount < allowed) { ++pcount; ++p_events; p = pi.next_prime(); }
      next = std::min(p, end);
    } else {
      while (p <= n) { ++pcount; ++p_events; p = pi.next_prime(); }
      if (pcount > allowed) throw std::runtime_error("unit starting point fails");
      next = std::min(end, n + (allowed - pcount) + 1);
    }
    U upper = pcount;
    if (mode == "unit") upper += next - n - 1;
    if (next <= n || W{SCALE} * upper * upper >= W{a} * qcount) {
      std::cerr << "FAILED n=" << n << " next=" << next << " P=" << upper << " Q=" << qcount << " allowed=" << allowed << '\n';
      throw std::runtime_error("strict cell predicate failed");
    }
    const W gap = W{a} * qcount - W{SCALE} * upper * upper;
    min_gap = std::min(min_gap, gap);
    const U width = next - n;
    min_width = std::min(min_width, width); max_width = std::max(max_width, width);
    const std::array<U, 7> row = {n, next, j, upper, qcount, lu, a};
    for (U v : row) word(out, v);
    n = next; ++cells;
    if ((cells & 262143) == 0) { out.flush(); std::cerr << "progress " << n << ' ' << cells << '\n'; }
    if (mode == "unit") while (p < n) { ++pcount; ++p_events; p = pi.next_prime(); }
  }
  out.close(); if (!out) throw std::runtime_error("certificate write");
  const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
  std::cout << "{\"status\":\"UNTRUSTED_NUMERICAL_FINITE_COVERAGE\",\"begin\":" << begin << ",\"end_exclusive\":" << end
   << ",\"mode\":\"" << mode << "\",\"cells\":" << cells << ",\"certificate_bytes\":" << cells * 56
   << ",\"initial_pi_begin_minus_one\":" << initialP << ",\"initial_pi_j\":" << initialQ
   << ",\"final_pi_end_minus_one\":" << pcount << ",\"p_events\":" << p_events << ",\"q_events\":" << q_events
   << ",\"min_width\":" << min_width << ",\"max_width\":" << max_width << ",\"min_integer_gap_low64\":" << static_cast<U>(min_gap)
   << ",\"min_integer_gap_high64\":" << static_cast<U>(min_gap >> 64) << ",\"seconds\":" << seconds << "}\n";
 } catch (const std::exception &e) { std::cerr << e.what() << '\n'; return 1; }
}
