#include <stdio.h>
#include <string.h>
double ramanujan_epsilon_bound(void);
int main(void){ double r=ramanujan_epsilon_bound(); unsigned long long u; memcpy(&u,&r,8); printf("%.17g %016llx\n", r, u); return 0; }
