#include <stdio.h>
#include <string.h>
double calibration_deviation(void);
int main(void){ double r=calibration_deviation(); unsigned long long u; memcpy(&u,&r,8); printf("%.17g %016llx\n", r, u); return 0; }
