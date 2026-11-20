/* Copyright (c) 2026 hschae. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: hschae and Codex
 */
// INDEPENDENT ORDINARY NUMERICAL CHECK. Not source-first PV.
// No primecount/primesieve library: quotient-count anchors + full byte sieve.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
using U=std::uint64_t;using W=__uint128_t;
U isqrt(U n){U r=static_cast<U>(std::sqrt(static_cast<long double>(n)));while(W{r+1}*(r+1)<=n)++r;while(W{r}*r>n)--r;return r;}
U anchor(U n){if(n<2)return 0;const U r=isqrt(n);std::vector<U>s(r+1),l(r+1);for(U i=1;i<=r;++i){s[i]=i-1;l[i]=n/i-1;}for(U p=2;p<=r;++p){if(s[p]==s[p-1])continue;const U before=s[p-1],stop=std::min(r,n/(p*p));for(U i=1;i<=stop;++i){const U ip=i*p,sub=ip<=r?l[ip]:s[n/ip];if(sub<before||l[i]<sub-before)throw std::runtime_error("anchor subtraction");l[i]-=sub-before;}for(U v=r;p*p<=v;--v){const U sub=s[v/p];if(sub<before||s[v]<sub-before)throw std::runtime_error("anchor small subtraction");s[v]-=sub-before;}}return l[1];}
struct Query{U point,value;};
std::vector<U> base_primes(U end){const U r=isqrt(end);std::vector<std::uint8_t>a(r+1,1);a[0]=a[1]=0;for(U p=2;p*p<=r;++p)if(a[p])for(U k=p*p;k<=r;k+=p)a[k]=0;std::vector<U>v;for(U p=3;p<=r;p+=2)if(a[p])v.push_back(p);return v;}
void check_counts(const std::vector<Query>&qs,U begin,U count,const std::vector<U>&ps,bool upper){
 if(qs.empty())throw std::runtime_error("empty queries");
 constexpr U BLOCK=U{1}<<25; //32MiB, 67million integers, transient
 U lo=begin+(begin%2==0);std::size_t qi=0;
 while(qi<qs.size()&&qs[qi].point<lo){if((upper?count>qs[qi].value:count!=qs[qi].value))throw std::runtime_error("initial count mismatch");++qi;}
 const U last=qs.back().point;
 std::vector<std::uint8_t> sieve;
 while(qi<qs.size()){
  const U size=std::min(BLOCK,(last-lo)/2+1),hi=lo+2*(size-1);
  sieve.assign(size,1);
  for(U p:ps){if(p*p>hi)break;U start=std::max(p*p,((lo+p-1)/p)*p);if(start%2==0)start+=p;if(start>hi)continue;for(U k=(start-lo)/2;k<size;k+=p)sieve[k]=0;}
  U cursor=0;
  while(qi<qs.size()&&qs[qi].point<=hi+1){const U stop=(qs[qi].point-lo)/2+1;count+=std::accumulate(sieve.begin()+static_cast<std::ptrdiff_t>(cursor),sieve.begin()+static_cast<std::ptrdiff_t>(stop),U{0});cursor=stop;if((upper?count>qs[qi].value:count!=qs[qi].value)){std::cerr<<"point="<<qs[qi].point<<" computed="<<count<<" certificate="<<qs[qi].value<<'\n';throw std::runtime_error("sieve count mismatch");}++qi;}
  count+=std::accumulate(sieve.begin()+static_cast<std::ptrdiff_t>(cursor),sieve.end(),U{0});lo=hi+2;
 }
}
U word(std::ifstream&f){U x=0;for(unsigned i=0;i<8;++i){int c=f.get();if(c<0)throw std::runtime_error("truncated row");x|=static_cast<U>(c)<<(8*i);}return x;}
int main(int argc,char**argv){try{
 if(argc!=5)throw std::runtime_error("usage: independent_finite_check CERT BEGIN END_EXCLUSIVE actual|unit");
 const auto start=std::chrono::steady_clock::now();const U begin=std::stoull(argv[2]),end=std::stoull(argv[3]);const bool upper=std::string(argv[4])=="unit";
 std::ifstream f(argv[1],std::ios::binary);if(!f)throw std::runtime_error("open");
 U elo=U{1}<<60,term=elo;for(U i=1;i<=20;++i){term/=i;elo+=term;}const U ehi=elo+22,F=U{1}<<60,scale=U{1}<<20;
 U expected=begin,cells=0;std::vector<Query> pq,qq;
 while(f.peek()!=EOF){std::array<U,7>r;for(auto&x:r)x=word(f);const auto[n,next,j,p,q,lu,a]=r;if(n!=expected||n>=next||next>end||n<38358837683ULL||end>1620000000001ULL||p>(U{1}<<40)||q>(U{1}<<40)||lu==0||lu>(U{1}<<46)||a>(U{1}<<60))throw std::runtime_error("cell domain/coverage");if(j!=W{n}*F/ehi||a!=W{n}*elo/lu||W{scale}*p*p>=W{a}*q)throw std::runtime_error("strict arithmetic");pq.push_back({next-1,p});qq.push_back({j,q});expected=next;++cells;}
 if(expected!=end||!cells)throw std::runtime_error("missing final endpoint");
 const auto ps=base_primes(end);const U ip=anchor(begin-1),iq=anchor(qq.front().point);
 check_counts(pq,begin,ip,ps,upper);check_counts(qq,qq.front().point+1,iq,ps,false);
 const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"{\"status\":\"INDEPENDENT_ORDINARY_ALL_COUNT_CHECK_PASS\",\"begin\":"<<begin<<",\"end_exclusive\":"<<end<<",\"cells\":"<<cells<<",\"initial_pi\":"<<ip<<",\"initial_q\":"<<iq<<",\"seconds\":"<<seconds<<",\"formal_verification\":false}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
