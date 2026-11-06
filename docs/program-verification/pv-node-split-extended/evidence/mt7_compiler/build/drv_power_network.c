#include <stdio.h>
#include <string.h>
double fks2_power_transport(void);
int main(void){ double r=fks2_power_transport(); unsigned long long u; memcpy(&u,&r,8); printf("%.17g %016llx\n", r, u); return 0; }
