// Deterministic integer-only sieve and error certificate (GNU C++17).
#include <cstdint>
#include <iostream>
#include <vector>
#include <array>
#include <algorithm>
#include <cassert>
using U=uint64_t; using S=int64_t; using X=__int128_t;
constexpr S W=1LL<<58, PAD=8192;
constexpr U N=195730000000ULL, H=100000000;
S gl,gh,tab[257];
S lg(U n,int offset=0){
 assert(n>0);
 int k=63-__builtin_clzll(n);
 U j=U((X(n)*256)>>k)-256;
 assert(j<256);
 X d=X(256+j)<<k;
 S z=S((256*X(n)-d)*W/d);
 S q=W/7;
 for(int i=6;i>=1;--i)q=W/i-S(X(z)*q/W);
 return (k-offset)*tab[256]+tab[j]+S(X(z)*q/W);
}
// lg(n)/W differs from ln n by <=128/W; ln ln n similarly <=256/W
// for n>=3 using derivative <=1 on arguments >=1.
S corr(U p){
 if(p<100)return lg(p)-lg(p-1)-W/p;
 S z=W/p, s=0;
 for(int k=2;k<=9;++k){z/=p;s+=z/k;}
 return s;
}
std::vector<int> primes;
void add(S &a,S b){S z; assert(!__builtin_add_overflow(a,b,&z)); a=z;}
void base(){
 std::vector<bool> seen(450000,false);
 for(int i=2;i<450000;i++)if(!seen[i]){
  primes.push_back(i);
  if(i<671)for(int j=i*i;j<450000;j+=i)seen[j]=true;
 }
}
// Calls: all odd primes and requested check points, in increasing order,
// with prime update before its check point.
template<class Prime,class Check>
void scan(U limit, U point,Prime p,Check c){
 p(2);
 const U block=1<<21;
 std::vector<unsigned char> s(block);
 for(U l=3;l<=limit;l+=2*block){
  U r=std::min(limit,l+2*block-2);
  std::fill(s.begin(),s.end(),0);
  for(U q:primes){
   if(q==2)continue;
   if(q*q>r)break;
   U u=std::max(q*q,((l+q-1)/q)*q);
   if(u%2==0)u+=q;
   for(U j=(u-l)/2;j<=(r-l)/2;j+=q)s[j]=1;
  }
  for(U j=0;j<=(r-l)/2;++j){
   U x=l+2*j;
   while(point<x && point<=limit)point=c(point);
   if(!s[j])p(x);
   if(point==x)point=c(point);
  }
 }
 while(point<=limit)point=c(point);
}
int main(){
 std::cin>>gl>>gh;for(S &a:tab)std::cin>>a;
 assert(std::cin && gl<gh);
 base();
 S c0=0,b0=0;U small=0;
 scan(H,H+1,[&](U p){small+=1;add(c0,corr(p));add(b0,lg(p)/S(p*(p-1)));},[](U x){return x+1;});
 // omitted all integers > H: reciprocal correction <= 1/H;
 // weighted <= 2(log H+1)/H < 40/H.
 S cl=c0-260*S(small),ch=c0+260*S(small)+W/H+1;
 S bl=b0-S(small)-PAD,bh=b0+2*S(small)+PAD+40*S(W/H+1);
 S ml=gl-ch,mh=gh-cl,wl=gl+bl,wh=gh+bh;
 std::cout<<"constant numerators scale 2^58: "<<gl<<" "<<gh<<" "<<ml<<" "<<mh<<" "<<wl<<" "<<wh<<std::endl;
 S A=0,B=0,C=0; U cnt=0,kc=0;
 // Half-open bins for calculation; proof covers both endpoints.
 const std::array<U,20> begin={100000,500000,800000,912560,1000000,1500000,
   2000000,2278382,2278383,2500000,3000000,4000000,5000000,8000000,
   10000000,20000000,30000000,50000000,100000000,9750000000ULL};
 constexpr unsigned J=begin.size();
 std::array<std::array<S,3>,J> maxc={};
 unsigned bin=0;
 S prevlo[3]={},prevhi[3]={};U last=0, checks=0;
 scan(N,begin[0],[&](U p){
  ++cnt;add(A,W/p);add(B,lg(p)/S(p));
  if(p<=H){add(C,corr(p));++kc;}
 },[&](U x){
   assert(A>=0 && A<8*W && B>=0 && B<29*W && C>=0 && C<W && cnt<=N);
   S l=lg(x),ll=lg(U(l),58);
   assert(l>=W && l<27*W && ll>0 && ll<4*W);
   S Clo=C-260*S(kc),Chi=C+260*S(kc);
   if(x>H){Clo=cl;Chi=ch;}
   S lo[3]={A-ll-mh-256,B-l+wl-S(cnt)-128-PAD,A+Clo-ll-gh-256};
   S hi[3]={A+S(cnt)-ll-ml+256,B+2*S(cnt)-l+wh+128+PAD,A+S(cnt)+Chi-ll-gl+256};
   if(last){
    S l0=lg(last),ll0=lg(U(l0),58);
    // Current lower and previous upper are replaced by monotone bounds
    // using the endpoint trend of the smooth subtraction.
    S diffs[3]={ll-ll0+512,l-l0+256,ll-ll0+512};
    U L=U(l+128+(1LL<<38)-1)>>38; // upper log(x) at scale 2^20
    if(last){
     while(bin+1<J && last>=begin[bin+1])++bin;
     assert(last>=begin[bin]);
     for(int i=0;i<3;++i){
      U mag=std::max({S(0),-prevlo[i]+diffs[i],hi[i]+diffs[i]});
      assert(mag<(U(1)<<53) && L<(U(1)<<25));
      X v=X(mag)*L*L;
      if(i!=1)v*=L;
      int bit=58+(i==1?40:60);
      v=(v+65535)>>16; bit-=16;
      S c=S((10000*v+(X(1)<<bit)-1)>>bit);
      maxc[bin][i]=std::max(maxc[bin][i],c);
     }
    }
   }
   for(int i=0;i<3;i++){prevlo[i]=lo[i];prevhi[i]=hi[i];}
   last=x;++checks;
   if(x==N)return N+1;
   U y=std::min(N,x+std::max(U(1),x>>19));
   for(U a:begin)if(x<a)y=std::min(y,a);
   return y;
 });
 assert(last==N && checks>0);
 std::cout<<"sieve endpoint "<<N<<", prime count "<<cnt<<", cells "<<checks-1<<std::endl;
 for(unsigned j=0;j<J;++j){
  std::cout<<"bin ["<<begin[j]<<","<<(j+1<J?begin[j+1]:N)<<"]; outward maxima /10000:";
  for(int i=0;i<3;++i)std::cout<<" "<<maxc[j][i];
  std::cout<<std::endl;
 }
}
