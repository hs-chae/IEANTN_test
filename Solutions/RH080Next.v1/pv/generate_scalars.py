#!/usr/bin/env python3
"""Generate source INPUT data and a restricted-C candidate, never result facts.

The only numerical literals emitted from the witness are its original nodal
coefficients, its scale, and its mesh. The C program computes every output.
The independent Lean syntax relation and actual modeled execution are separate.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
INPUT = ROOT / 'Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs/w4.json'
INPUT_SHA = '61f745f27018ea5addbb01c1d583b128b2639b0f101d764136c98c26983c5521'


def need(value, message):
    if not value:
        raise ValueError(message)


def tree(values, lo, hi):
    if hi-lo == 1:
        return 'return ' + str(values[lo]) + 'ULL;'
    mid = (lo+hi)//2
    return ('if (j < '+str(mid)+'ULL) { '+tree(values, lo, mid)+
            ' } else { '+tree(values, mid, hi)+' }')


def main():
    raw = INPUT.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == INPUT_SHA, 'Frozen w4 input identity differs')
    d = json.loads(raw)
    need(d['m'] == 360 and d['scale'] == 10**16 and len(d['coefficients']) == 2520,
         'Expected actual radius-seven window')
    scale = d['scale']
    encoded = [scale+x for x in d['coefficients']]
    need(all(0 <= x < 2*scale for x in encoded), 'Encoded node outside supported word fragment')
    source = '''/*
Copyright (c) 2026 IEANTN contributors. Apache-2.0.
Authors: OpenAI (Codex).
Fixed rational input; every reported scalar is computed by the loops below.
*/
#include <stdint.h>
#include <stdio.h>

uint64_t encoded_node(uint64_t j) {
  if (j >= 2520ULL) { return 10000000000000000ULL; }
  ''' + tree(encoded, 0, len(encoded)) + '''
}

uint64_t positive_part(uint64_t e) {
  if (e >= 10000000000000000ULL) { return (e - 10000000000000000ULL); }
  return 0ULL;
}

uint64_t negative_part(uint64_t e) {
  if (e < 10000000000000000ULL) { return (10000000000000000ULL - e); }
  return 0ULL;
}

uint64_t absolute_difference(uint64_t a, uint64_t b) {
  if (a >= b) { return (a - b); }
  return (b - a);
}

uint64_t muldiv_ceil(uint64_t a, uint64_t b, uint64_t d) {
  if (d == 0ULL) { return 0ULL; }
  uint64_t q = 0ULL;
  uint64_t r = 0ULL;
  uint64_t power = 9223372036854775808ULL;
  while (power > 0ULL) {
    uint64_t bit = ((b / power) % 2ULL);
    uint64_t t = ((2ULL * r) + (bit * a));
    q = ((2ULL * q) + (t / d));
    r = (t % d);
    power = (power / 2ULL);
  }
  if (r > 0ULL) { q = (q + 1ULL); }
  return q;
}

uint64_t f0_positive(void) {
  uint64_t sum = positive_part(encoded_node(0ULL));
  uint64_t j = 1ULL;
  while (j < 2520ULL) {
    sum = (sum + (2ULL * positive_part(encoded_node(j))));
    j = (j + 1ULL);
  }
  return sum;
}

uint64_t f0_negative(void) {
  uint64_t sum = negative_part(encoded_node(0ULL));
  uint64_t j = 1ULL;
  while (j < 2520ULL) {
    sum = (sum + (2ULL * negative_part(encoded_node(j))));
    j = (j + 1ULL);
  }
  return sum;
}

uint64_t f0_numerator(void) {
  return (f0_positive() - f0_negative());
}

uint64_t positive_area_numerator(void) {
  uint64_t sum = 0ULL;
  uint64_t j = 360ULL;
  while (j < 2520ULL) {
    uint64_t left = encoded_node(j);
    uint64_t right = encoded_node((j + 1ULL));
    uint64_t a = positive_part(left);
    uint64_t b = positive_part(right);
    if (left >= 10000000000000000ULL) {
      if (right >= 10000000000000000ULL) {
        sum = (sum + (a + b));
      } else {
        uint64_t neg = negative_part(right);
        sum = (sum + muldiv_ceil(a, a, (a + neg)));
      }
    } else {
      if (right > 10000000000000000ULL) {
        uint64_t neg = negative_part(left);
        sum = (sum + muldiv_ceil(b, b, (b + neg)));
      }
    }
    j = (j + 1ULL);
  }
  return sum;
}

uint64_t component_height_numerator(void) {
  uint64_t sum = positive_part(encoded_node(360ULL));
  uint64_t j = 360ULL;
  while (j < 2520ULL) {
    uint64_t a = positive_part(encoded_node(j));
    uint64_t b = positive_part(encoded_node((j + 1ULL)));
    if (b > a) { sum = (sum + (b - a)); }
    j = (j + 1ULL);
  }
  return sum;
}

uint64_t first_variation_numerator(void) {
  uint64_t sum = 0ULL;
  uint64_t j = 0ULL;
  while (j < 2520ULL) {
    uint64_t a = encoded_node(j);
    uint64_t b = encoded_node((j + 1ULL));
    sum = (sum + absolute_difference(a, b));
    j = (j + 1ULL);
  }
  return (2ULL * sum);
}

uint64_t derivative_variation_numerator(void) {
  uint64_t sum = absolute_difference(encoded_node(1ULL), encoded_node(0ULL));
  uint64_t j = 0ULL;
  while (j < 2520ULL) {
    uint64_t a = encoded_node(j);
    uint64_t b = encoded_node((j + 1ULL));
    uint64_t c = encoded_node((j + 2ULL));
    sum = (sum + absolute_difference((a + c), (2ULL * b)));
    j = (j + 1ULL);
  }
  return ((2ULL * 360ULL) * sum);
}

uint64_t second_moment_numerator(void) {
  uint64_t sum = 0ULL;
  uint64_t j = 0ULL;
  while (j < 2520ULL) {
    uint64_t a = absolute_difference(encoded_node(j), 10000000000000000ULL);
    uint64_t b = absolute_difference(encoded_node((j + 1ULL)), 10000000000000000ULL);
    a = ((a + 9999999ULL) / 10000000ULL);
    b = ((b + 9999999ULL) / 10000000ULL);
    uint64_t left = (((6ULL * (j * j)) + (4ULL * j)) + 1ULL);
    uint64_t right = (((6ULL * (j * j)) + (8ULL * j)) + 3ULL);
    sum = (sum + ((a * left) + (b * right)));
    j = (j + 1ULL);
  }
  return sum;
}

uint64_t maximum_numerator(void) {
  uint64_t maximum = 0ULL;
  uint64_t j = 0ULL;
  while (j < 2520ULL) {
    uint64_t value = absolute_difference(encoded_node(j), 10000000000000000ULL);
    if (value > maximum) { maximum = value; }
    j = (j + 1ULL);
  }
  return maximum;
}

int main(void) {
  printf("%llu\\n", (unsigned long long)f0_numerator());
  printf("%llu\\n", (unsigned long long)positive_area_numerator());
  printf("%llu\\n", (unsigned long long)component_height_numerator());
  printf("%llu\\n", (unsigned long long)first_variation_numerator());
  printf("%llu\\n", (unsigned long long)derivative_variation_numerator());
  printf("%llu\\n", (unsigned long long)second_moment_numerator());
  printf("%llu\\n", (unsigned long long)maximum_numerator());
  return 0;
}
'''
    (HERE/'window_scalars.c').write_text(source)
    (HERE/'w4.json').write_bytes(raw)
    print(json.dumps({'source_bytes':len(source.encode()),'input_sha256':INPUT_SHA,
                      'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
                      'output_facts_generated':False}))


if __name__ == '__main__':
    main()
