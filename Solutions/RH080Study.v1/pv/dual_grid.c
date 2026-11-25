/* Copyright (c) 2026 IEANTN contributors. Apache-2.0. */
#include <stdint.h>
#include <stdio.h>

uint64_t jump_positive(uint64_t j) {
  if (j == 4ULL) { return 837ULL; }
  if (j == 7ULL) { return 251ULL; }
  if (j == 9ULL) { return 249ULL; }
  if (j == 11ULL) { return 176ULL; }
  if (j == 15ULL) { return 111ULL; }
  if (j == 17ULL) { return 82ULL; }
  if (j == 19ULL) { return 18ULL; }
  return 0ULL;
}

uint64_t jump_negative(uint64_t j) {
  if (j == 5ULL) { return 621ULL; }
  if (j == 6ULL) { return 129ULL; }
  if (j == 8ULL) { return 229ULL; }
  if (j == 10ULL) { return 170ULL; }
  if (j == 12ULL) { return 119ULL; }
  if (j == 13ULL) { return 23ULL; }
  if (j == 14ULL) { return 15ULL; }
  if (j == 16ULL) { return 103ULL; }
  if (j == 18ULL) { return 59ULL; }
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

uint64_t sample_bound(uint64_t k) {
  if (k == 0ULL) { return 1220704ULL; }
  uint64_t positive = 0ULL;
  uint64_t negative = 0ULL;
  uint64_t j = 1ULL;
  while (j <= 20ULL) {
    uint64_t r = ((j * k) % 512ULL);
    uint64_t flipped = 0ULL;
    if (r > 256ULL) { r = (512ULL - r); flipped = 1ULL; }
    if (r > 128ULL) { r = (256ULL - r); }
    uint64_t sine = sine_fixed(r);
    uint64_t a = jump_positive(j);
    uint64_t b = jump_negative(j);
    if (flipped == 0ULL) {
      positive = (positive + (a * sine));
      negative = (negative + (b * sine));
    } else {
      positive = (positive + (b * sine));
      negative = (negative + (a * sine));
    }
    j = (j + 1ULL);
  }
  uint64_t absolute = 0ULL;
  if (positive >= negative) { absolute = (positive - negative); }
  else { absolute = (negative - positive); }
  uint64_t numerator = (((absolute + 255ULL) / 256ULL) * 256000000ULL);
  uint64_t denominator = ((2ULL * 3141592653ULL) * k);
  return (((numerator + denominator) - 1ULL) / denominator) + 200ULL;
}

uint64_t rh_dual_bound(void) {
  uint64_t maximum = 0ULL;
  uint64_t k = 0ULL;
  while (k <= 256ULL) {
    uint64_t value = sample_bound(k);
    if (value > maximum) { maximum = value; }
    k = (k + 1ULL);
  }
  return maximum;
}

int main(void) {
  printf("%llu\n", (unsigned long long)rh_dual_bound());
  return 0;
}
