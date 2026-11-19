
/* Independent finite certificate for mertens.md; no libm, no prime table.
   Build: /usr/bin/gcc -std=gnu11 -O3 -Wall -Wextra sieve.c -o /work/mertens-check
   Run:   /work/mertens-check
   Requires __int128 (GCC extension). Do not compile with -DNDEBUG. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>

typedef __int128 I;
typedef struct { I l,h; } B;
#define S (((I)1)<<60)
#define N 100000000u
static unsigned char mark[(N>>4)+1];

static I updiv(I a,I b) { assert(a>=0 && b>0); return (a+b-1)/b; }
static B add(B a,B b) { return (B){a.l+b.l,a.h+b.h}; }
static B sub(B a,B b) { return (B){a.l-b.h,a.h-b.l}; }
static B quot(B a,I n) { assert(a.l>=0); return (B){a.l/n,updiv(a.h,n)}; }
static B rat(I n,I d) { assert(n>=0); return (B){n*S/d,updiv(n*S,d)}; }
/* Below, inputs of prod_up are nonnegative and the products fit I. */
static I prod_up(I a,I b) {
    I c;
    int overflow=__builtin_mul_overflow(a,b,&c);
    assert(!overflow && a>=0 && b>=0);
    return updiv(c,S);
}
static I prod_lo(I a,I b) {
    I c;
    int overflow=__builtin_mul_overflow(a,b,&c);
    assert(!overflow && a>=0 && b>=0);
    return c/S;
}

/* Return log(a/b) when b<=a<=2b. Dyadic fixed point, rigorous remainder. */
static B small_log(I a,I b) {
    assert(b>0 && a>=b && a<=2*b);
    I z=(a-b)*S/(a+b), z2=z*z/S, v=z, out=0;
    for(int j=0;j<20;++j) {
        out+=v/(2*j+1);
        v=v*z2/S;
    }
    return (B){2*out,2*out+128};
}
static B log2q;
static B log_ratio(I a,I b) {
    assert(a>0&&b>0);
    if (a<b) { B t=log_ratio(b,a); return (B){-t.h,-t.l}; }
    int k=0;
    while (a>=2*b) { b*=2; ++k; }
    B r=small_log(a,b);
    return (B){r.l+k*log2q.l,r.h+k*log2q.h};
}
static B log_int(unsigned n) { return log_ratio(n,1); }
static B log_log(B t) {
    assert(t.l>0);
    return (B){log_ratio(t.l,S).l,log_ratio(t.h,S).h};
}
static unsigned composite(unsigned n) {
    if((n&1)==0) return n!=2;
    return (mark[n>>4]>>((n>>1)&7))&1u;
}
static void sieve(void) {
    for(unsigned p=3;p*p<=N;p+=2) if(!composite(p))
        for(unsigned q=p*p;q<=N;q+=2*p)
            mark[q>>4]|=1u<<((q>>1)&7);
}

/* Bounds, in units 1/100000, for d_Q L^3,d_1 L^3,d_2 L^2.
   Each row is checked up to N; rows can overlap. A zero disables a test.
   d_Q is the logarithmic error, not the relative error. */
static const unsigned rows[][4]={
    {2278382,19998,0,0},
    {2278383,0,19999,0},
    {912566,0,0,29900},
    {2300000,19850,19850,0},
    {3000000,19850,19850,21200},
    {5000000,15020,15020,16180},
    {10000000,11970,11970,12740},
    {20000000,8880,8880,9490},
    {30000000,8820,8820,9350},
    {50000000,7110,7110,7580}
};
#define ROWCOUNT (sizeof(rows)/sizeof(rows[0]))
static B G,M,C3;
static void print_positive(I a) {
    assert(a>=0);
    if(a>=10) print_positive(a/10);
    putchar('0'+(int)(a%10));
}
static void emit_anchor(unsigned p,unsigned q,B r0,B r1,B r2) {
    printf("anchor %u %u",p,q);
    B t[3]={r0,r1,r2};
    for (int j=0;j<3;++j) {
        putchar(' '); print_positive(t[j].l);
        putchar(' '); print_positive(t[j].h);
    }
    putchar('\n');
}

/* On [p,q) the arithmetic sums are constant. Use the left limit at q. */
static void segment(unsigned p,unsigned q,B Lp,B Lq,B logQ,B s1,B s2) {
    B d[3];
    B llp=log_log(Lp), llq=log_log(Lq);
    B r0=sub(logQ,G),r1=sub(s1,M),r2=add(s2,C3);
    if((p<2278382 && q>2278383) || (p<912560 && q>912566)) emit_anchor(p,q,r0,r1,r2);
    d[0]=(B){r0.l-llq.h,r0.h-llp.l};
    d[1]=(B){r1.l-llq.h,r1.h-llp.l};
    d[2]=(B){r2.l-Lq.h,r2.h-Lp.l};
    /* A positive lower bound on all segments; prove at the worst end for d,
       and the smaller endpoint for the positive multiplying factors. */
    unsigned lo=1,hi=10001;
    while(hi-lo>1) { unsigned a=(lo+hi)/2; if(a*a<=p) lo=a; else hi=a; }
    for(unsigned j=0;j<2;++j) {
        assert(d[j].l>0);
        assert(prod_lo(d[j].l*lo,Lp.l)>rat(3,1000).h);
    }
    assert(d[2].l*lo>rat(1,10).h);

    if(q>10000) {
        if(p<10000) {
            printf("clipped auxiliary segment %u %u at 10000\n",p,q);
            B t=log_int(10000), u=log_log(t);
            d[0].h=r0.h-u.l; d[1].h=r1.h-u.l; d[2].h=r2.h-t.l;
        }
        unsigned h=lo;
        while(h*h<q) ++h;
        assert(prod_up(d[0].h*h,Lq.h)<rat(170,100).l);
        assert(prod_up(d[1].h*h,Lq.h)<rat(170,100).l);
        assert(d[2].h*h<rat(188,100).l);
    }
    for(unsigned i=0;i<ROWCOUNT;++i) if(q>=rows[i][0]) {
        I bound[3]={d[0].h,d[1].h,d[2].h};
        if(p<rows[i][0]) {
            B a=log_int(rows[i][0]), b=log_log(a);
            bound[0]=r0.h-b.l;
            bound[1]=r1.h-b.l;
            bound[2]=r2.h-a.l;
        }
        for(unsigned j=0;j<3;++j) if(rows[i][1+j]) {
            I v=prod_up(prod_up(bound[j],Lq.h),Lq.h);
            if(j!=2) v=prod_up(v,Lq.h);
            I cap=rat(rows[i][1+j],100000).l;
            if(!(v<cap)) {
                fprintf(stderr,"row %u column %u segment %u..%u; scaled error approx %lld / 10^9\n",
                   i,j,p,q,(long long)(v*1000000000/S));
                assert(v<cap);
            }
        }
    }
}

int main(void) {
    log2q=small_log(2,1);
    sieve();
    unsigned n=1000000;
    B hn={0,0};
    for(unsigned i=1;i<=n;++i) hn=add(hn,rat(1,i));
    G=sub(sub(hn,log_int(n)),rat(1,2*n));
    G.h+=rat(1,(I)n*n).h;
    B C={0,0}, W={0,0};
    unsigned count=0;
    for(unsigned p=2;p<=N;++p) if(!composite(p)) {
        ++count;
        B lp=log_int(p);
        C=add(C,sub(small_log(p,p-1),rat(1,p)));
        W=add(W,quot(lp,(I)p*(p-1)));
    }
    /* Both higher-power tails are positive. See mertens.md for bounds. */
    C.h+=rat(1,12*(I)N).h;
    W.h+=rat(102,100*(I)N).h;
    M=sub(G,C); C3=add(G,W);
    B logQ={0,0}, s1={0,0}, s2={0,0}, Lprev={0,0};
    unsigned prev=0;
    for(unsigned p=2;p<=N;++p) if(!composite(p)) {
        B l=log_int(p);
        if(prev) segment(prev,p,Lprev,l,logQ,s1,s2);
        logQ=add(logQ,small_log(p,p-1));
        s1=add(s1,rat(1,p));
        s2=add(s2,quot(l,p));
        prev=p; Lprev=l;
    }
    segment(prev,N,Lprev,log_int(N),logQ,s1,s2);
    printf("finite Mertens certificate passed; N=%u, prime count=%u\n",N,count);
    return 0;
}
