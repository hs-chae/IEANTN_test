/* Exact finite checks. Build with gcc -O3 sieve.c -o /work/sieve.
   No floating-point or external primes. Prefix interval bounds use scale 2^58. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>
#include <string.h>
typedef __uint128_t U;
typedef __int128 I;
typedef uint64_t Z;
static const Z S=(1ULL<<58);
static Z lg2;

/* Returns a lower bound on S*log(1+2z/(1-z)), error <128 units,
   when the exact argument z in [0,1/3] was rounded down to z/S.
   Power recurrence accumulates <4 units per power (a contraction);
   total divided terms and tail contribute <128 units. */
static Z atanh2(Z z){
    Z y=(U)z*z/S, t=z,s=0;
    for(unsigned i=1;i<=63;i+=2){
        s+=t/i;
        t=(U)t*y/S;
    }
    return 2*s;
}
/* log(n), for 1 <= n < 2^67. Lower error <128*(k+1). */
static Z ln0(U n){
    U q=1; unsigned k=0;
    while(q<=n/2){q*=2;k++;}
    assert(k<67);
    Z z=(n-q)*S/(n+q);
    return lg2*k+atanh2(z);
}
/* S*loglog(n), used only for n>=1000; lower with error <= 18000 units. */
static Z ll0(Z n){
    return ln0(ln0(n))-58*(lg2+128);
}

static Z sqrt_floor(Z a){
    Z x=0;
    for (Z b=1ULL<<20;b;b>>=1) if((x+b)*(x+b)<=a) x+=b;
    return x;
}

static U loP=0,hiP=0,loV=0,hiV=0,loW=0,hiW=0;
static U loCorrP=0,hiCorrP=0,loCorrW=0,hiCorrW=0;

/* Accurate gamma interval obtained by harmonic sum plus trapezoid;
   proof in candidate. */
static U gamma_lo, gamma_hi;
static void gamma_init(void){
    const Z n=1000000;
    U h=0;
    for (Z i=1;i<=n;i++)h+=S/i;
    gamma_lo=h-ln0(n)-10000-(S/(2*n)+1);
    gamma_hi=h+n-ln0(n)-S/(2*n)+1+S/(n*n)+1;
}

/* Run finite sieve on [2,B]. For tested blocks [a,b] it certifies the
   product and the two prime sums for EVERY real x in [a,b].
   Block endpoints are shared. Arguments: A B PROD_NUM SUM_NUM WEIGHT_NUM
   with coefficients divided by 1000. Use 0 to skip an output. */
int main(int argc,char **argv){
    if(argc!=6 && argc!=7)return 2;
    int sqmode=argc==7 && !strcmp(argv[6],"sqrt");
    if(argc==7 && !sqmode)return 2;
    Z A=strtoull(argv[1],0,10), B=strtoull(argv[2],0,10);
    Z cP=atoi(argv[3]),cV=atoi(argv[4]),cW=atoi(argv[5]);
    assert(1000<=A && A<B && B<=75000000000 && cP<=(sqmode?7000:500) && cV<=(sqmode?7000:500) && cW<=(sqmode?7000:500));
    lg2=atanh2(S/3);
    gamma_init();
    unsigned lim=1;while((Z)lim*lim<=B)lim++;
    unsigned *pr=malloc(lim*sizeof(unsigned)),npr=0;
    unsigned char *lp=calloc(lim,1);
    assert(pr && lp);
    for(unsigned i=2;i<lim;i++)if(!lp[i]){
        pr[npr++]=i;
        for(Z j=(Z)i*i;j<lim;j+=i)lp[j]=1;
    }
    const Z M=10000000; /* constants: p<=M from sieve; tails via Dusart 4.2 */
    unsigned char *cs=calloc(M+1,1);assert(cs);
    for(Z n=2;n<=M;n++)if(!cs[n]){
        for(Z j=n*n;j<=M;j+=n)cs[j]=1;
        U q=(U)n*n;unsigned k=2;
        while(1){
            Z term=S/(q*k);
            if(!term)break;
            loCorrP+=term;++k;q*=n;
        }
        hiCorrP+=k+1;
        if(cW){
            Z l=ln0(n);
            U den=(U)n*(n-1);
            loCorrW+=l/den;hiCorrW+=(l+10000)/den+1;
        }
    }
    hiCorrP+=loCorrP;
    /* Certified tails independent of finite verification outputs. */
    loCorrP+=(U)S*28/10000000000ULL;     /* 2.8e-9 */
    hiCorrP+=(U)S*31/10000000000ULL+1;   /* 3.1e-9 */
    loCorrW+=(U)S*997/(1000*M);
    hiCorrW+=(U)S*1004/(1000*M)+1;
    free(cs);
    const Z ZB=1<<21;
    unsigned char *seg=malloc(ZB);assert(seg);
    Z a=2,b=2;
    U p0=0,v0=0,w0=0,bv_low=0,bv_hi=0;
    Z cnt=0,blocks=0; unsigned failP=0,failV=0,failW=0;
    Z maxBadP=0,maxBadV=0,maxBadW=0;
    for(Z low=2;low<=B;low+=ZB){
        Z high=low+ZB-1;if(high>B)high=B;
        memset(seg,0,high-low+1);
        for(unsigned j=0;j<npr;j++){
            Z p=pr[j],s=p*p;
            if(s>high)break;
            if(s<low)s=((low+p-1)/p)*p;
            for(Z k=s;k<=high;k+=p)seg[k-low]=1;
        }
        for(Z n=low;n<=high;n++){
            if(!seg[n-low]){
                ++cnt;
                if(cW && n<=10000){
                    Z l=ln0(n);
                    loW+=l/n;hiW+=(l+10000)/n+1;
                }
                Z first=S/n;
                loV+=first;hiV+=first+1;
                U q=(U)n*n; unsigned k=2;
                Z x=0;
                while(1){
                    Z term=S/(q*k);
                    if(!term)break;
                    x+=term;++k;q*=n;
                }
                loP+=first+x;hiP+=first+x+k+2;

            }
            if(n==b){
                if(cW && a>=10000){
                    U vl=loV-bv_low,vu=hiV-bv_hi;
                    {
                        /* On (a,b], log p/p = (log a-1)/p + 1/a minus
                           a nonnegative error <= (b-a)^2/(2a^2 p).
                           Initial primes p<=10000 are computed directly. */
                        U er=(U)(b-a)*(b-a)*S/(2*(U)a*a)+1;
                        Z l=ln0(a);
                        I alpha=(I)l-S;
                        I beta=alpha+10000;
                        I lowW=(alpha-(I)er)*(I)((alpha-(I)er)>=0?vl:vu)/(I)S
                                 +(I)((U)cnt*S/a)-2;
                        I upW=beta*(I)(beta>=0?vu:vl)/(I)S+(I)((U)cnt*S/a)+2;
                        loW+=lowW;hiW+=upW;
                    }
                }
                if(a>=A){
                    ++blocks;
                    Z bll=ll0(b), all=ll0(a);
                    Z alb=ln0(b), ala=ln0(a);
                    /* Conservative denominator: integer ceiling of 1024 log b. */
                    Z h=((U)(alb+10000)*1024+S-1)/S;
                    U h2=(U)h*h,h3=h2*h;
                    Z v=sqmode?sqrt_floor(b)+1:0;
                    U den=sqmode?(U)v*h:h3;
                    U num=sqmode?1024:(U)1024*1024*1024;
                    if(cP){
                        /* Certify both reciprocal product relative errors. */
                        /* If target q=n/d, s<=q/(1+q)
                           suffices since exp(s)<=1/(1-s). */
                        U n=(U)cP*num,d=1000*den;
                        U w=S*n/(d+n);
                        if((I)p0-(I)gamma_hi-(I)bll-18000<=-(I)w ||
                           (I)hiP-(I)gamma_lo-(I)all>=(I)w) {++failP;maxBadP=b;}
                    }
                    if(cV){
                        U w=(U)cV*S*num/(1000*den);
                        I mlo=(I)gamma_lo-(I)hiCorrP;
                        I mhi=(I)gamma_hi-(I)loCorrP;
                        if((I)v0-mhi-(I)bll-18000<=-(I)w ||
                           (I)hiV-mlo-(I)all>=(I)w) {++failV;maxBadV=b;}
                    }
                    if(cW){
                        U w=sqmode?(U)cW*S/(1000*v):(U)cW*S*1024*1024/(1000*h2);
                        U blo=gamma_lo+loCorrW, bhi=gamma_hi+hiCorrW;
                        if((I)w0+(I)blo-(I)alb-10000<=-(I)w ||
                           (I)hiW+(I)bhi-(I)ala>=(I)w) {++failW;maxBadW=b;}
                    }
                }
                a=b;
                /* Geometric spacing with per-block variation much tighter
                   than targets. At small p check constants, but do not split every integer. */
                Z step=a/20000+1;
                if(sqmode && a>=A){
                    Z cap=sqrt_floor(a)/16+1;
                    if(step>cap)step=cap;
                }
                if(a<A && a+step>A)step=A-a;
                if(a<10000 && a+step>10000)step=10000-a;
                if(a>=A && a<M && a+step>M)step=M-a;
                if(a<M && a+step>M)step=M-a;
                if(step>B-a)step=B-a;
                b=a+step;
                p0=loP;v0=loV;w0=loW;bv_low=loV;bv_hi=hiV;cnt=0;
            }
        }
    }
    printf("A=%" PRIu64 " B=%" PRIu64 " blocks=%" PRIu64
           " failures=(%u,%u,%u) last failing right endpoints=(%" PRIu64 ",%" PRIu64 ",%" PRIu64 ")\n",
           A,B,blocks,failP,failV,failW,maxBadP,maxBadV,maxBadW);
    return (failP || failV || failW)?1:0;
}
