/* Exact odd-only segmented Eratosthenes, counts near PT endpoint. */
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
typedef uint64_t Z;
int main(void){
    const Z N=38358837682ULL, B=N+50, K=14111427770ULL;
    unsigned root=1;while((Z)root*root<=B)root++;
    unsigned *pr=malloc(root*sizeof(unsigned)),npr=0;
    unsigned char *small=calloc(root,1);
    assert(pr && small);
    for (unsigned i=3;i<root;i+=2)if(!small[i]){
        pr[npr++]=i;
        for (Z j=(Z)i*i;j<root;j+=2*i)small[j]=1;
    }
    const unsigned M=1<<20;
    unsigned char *seg=malloc(M);
    assert(seg);
    Z cnt=1; /* prime 2 */
    for (Z a=3;a<=B;a+=2*M){
        Z last=a+2*(M-1);
        if(last>B)last=(B-1)|1;
        unsigned len=(last-a)/2+1;
        memset(seg,0,len);
        for(unsigned j=0;j<npr;j++){
            Z p=pr[j],s=p*p;
            if(s>last)break;
            if(s<a){
                s=((a+p-1)/p)*p;
                if(!(s&1))s+=p;
            }
            for(Z i=(s-a)/2;i<len;i+=p)seg[i]=1;
        }
        for(unsigned j=0;j<len;j++){
            cnt+=1-seg[j];
            Z n=a+2*j;
            if((K-35<=n && n<=K+35)||(N-10<=n && n<=N+10))
                printf("%" PRIu64 " %" PRIu64 " %u\n",n,cnt,1-seg[j]);
        }
    }
    return 0;
}
