#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
uint64_t rh_coeff(uint64_t n);
int main(void) {
    for (uint64_t j=0; j<=20; ++j) {
        if (printf("%" PRIu64 " %" PRIu64 "\n", j, rh_coeff(j))<0) return 1;
    }
    return 0;
}
