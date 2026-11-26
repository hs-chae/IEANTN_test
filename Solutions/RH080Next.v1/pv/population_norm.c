/* Copyright (c) 2026 IEANTN contributors. Apache-2.0. */
#include <stdint.h>
#include <stdio.h>

uint64_t coefficient(uint64_t j) {
  if (j == 0ULL) { return 546871713113309800ULL; }
  if (j == 1ULL) { return 546871713113309600ULL; }
  if (j == 2ULL) { return 546871713113309600ULL; }
  if (j == 3ULL) { return 546871713113309600ULL; }
  if (j == 4ULL) { return 546871713113309600ULL; }
  if (j == 5ULL) { return 546871713113309600ULL; }
  if (j == 6ULL) { return 515419762691595100ULL; }
  if (j == 7ULL) { return 357059942573668200ULL; }
  if (j == 8ULL) { return 119725872611533800ULL; }
  return 0ULL;
}

uint64_t sine_fixed(uint64_t r) {
  uint64_t z = ((3141592654ULL * r) / 256ULL);
  uint64_t term = z;
  uint64_t positive = z;
  uint64_t negative = 0ULL;
  uint64_t n = 1ULL;
  while (n <= 8ULL) {
    term = ((((term * z) / 1000000000ULL) * z) / 1000000000ULL);
    term = (term / ((2ULL * n) * ((2ULL * n) + 1ULL)));
    if ((n % 2ULL) == 0ULL) { positive = (positive + term); }
    else { negative = (negative + term); }
    n = (n + 1ULL);
  }
  return (positive - negative);
}

uint64_t coefficient_times_sine(uint64_t a, uint64_t s) {
  uint64_t high = (a / 1000000000ULL);
  uint64_t low = (a % 1000000000ULL);
  return ((high * s) + ((low * s) / 1000000000ULL));
}

uint64_t sample_upper(uint64_t k) {
  uint64_t positive = 0ULL;
  uint64_t negative = 0ULL;
  uint64_t j = 0ULL;
  while (j < 16ULL) {
    uint64_t a = coefficient(j);
    if (a > 0ULL) {
      uint64_t r = ((((2ULL * j) * k) + 128ULL) % 512ULL);
      uint64_t flipped = 0ULL;
      if (r > 256ULL) { r = (512ULL - r); flipped = 1ULL; }
      if (r > 128ULL) { r = (256ULL - r); }
      uint64_t s = sine_fixed(r);
      uint64_t term = coefficient_times_sine(a, s);
      if (j > 0ULL) { term = (2ULL * term); }
      if (flipped == 0ULL) { positive = (positive + term); }
      else { negative = (negative + term); }
    }
    j = (j + 1ULL);
  }
  uint64_t absolute = 0ULL;
  if (positive >= negative) { absolute = (positive - negative); }
  else { absolute = (negative - positive); }
  return (absolute + 100000000000000ULL);
}

uint64_t chord_upper(void) {
  uint64_t sum = 0ULL;
  uint64_t j = 0ULL;
  while (j < 16ULL) {
    uint64_t a = coefficient(j);
    uint64_t factor = ((20ULL * j) * j);
    uint64_t high = (a / 196608ULL);
    uint64_t low = (a % 196608ULL);
    uint64_t term = ((high * factor) + ((((low * factor) + 196608ULL) - 1ULL) / 196608ULL));
    sum = (sum + term);
    j = (j + 1ULL);
  }
  return sum;
}

uint64_t population_norm_upper(void) {
  uint64_t sum = 0ULL;
  uint64_t k = 0ULL;
  while (k < 256ULL) {
    uint64_t value = sample_upper(k);
    sum = (sum + ((value + 255ULL) / 256ULL));
    k = (k + 1ULL);
  }
  return (sum + chord_upper());
}

int main(void) {
  printf("%llu\n", (unsigned long long)population_norm_upper());
  return 0;
}
