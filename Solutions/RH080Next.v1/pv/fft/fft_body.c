/* Original w4 fixed-input periodic FFT port. Numerical observation is NOT PV.
   Base 10^9, five magnitude limbs + sign, fixed unit 10^36. */
uint64_t zero_words(uint64_t *a, uint64_t n) {
  uint64_t j=0ULL; while (j<n) { a[j]=0ULL; j=(j+1ULL); } return 0ULL;
}
uint64_t copy_words(uint64_t *out, uint64_t *in, uint64_t n) {
  uint64_t j=0ULL; while(j<n) {out[j]=in[j];j=(j+1ULL);}return 0ULL;
}
uint64_t increment_words(uint64_t *a,uint64_t n) {
  uint64_t j=0ULL;uint64_t carry=1ULL;
  while(j<n){uint64_t t=(a[j]+carry);a[j]=(t%1000000000ULL);carry=(t/1000000000ULL);j=(j+1ULL);}return carry;
}
uint64_t multiply_small(uint64_t *a,uint64_t n,uint64_t m) {
  uint64_t j=0ULL;uint64_t carry=0ULL;
  while(j<n){uint64_t t=((a[j]*m)+carry);a[j]=(t%1000000000ULL);carry=(t/1000000000ULL);j=(j+1ULL);}return carry;
}
uint64_t divide_small(uint64_t *a,uint64_t n,uint64_t d,uint64_t ceiling) {
  uint64_t j=n;uint64_t rem=0ULL;
  while(j>0ULL){j=(j-1ULL);uint64_t t=((rem*1000000000ULL)+a[j]);a[j]=(t/d);rem=(t%d);}
  if(ceiling>0ULL){if(rem>0ULL){return increment_words(a,n);}}return 0ULL;
}
uint64_t magnitude_compare(uint64_t *a,uint64_t *b) {
  uint64_t j=5ULL;while(j>0ULL){j=(j-1ULL);if(a[j]>b[j]){return 2ULL;}if(a[j]<b[j]){return 0ULL;}}return 1ULL;
}
uint64_t canonical_sign(uint64_t *a) {
  uint64_t nonzero=0ULL;uint64_t j=0ULL;while(j<5ULL){nonzero=(nonzero+a[j]);j=(j+1ULL);}if(nonzero==0ULL){a[5ULL]=0ULL;}return 0ULL;
}
uint64_t fixed_add(uint64_t *out,uint64_t *a,uint64_t *b,uint64_t subtract) {
  uint64_t as=a[5ULL];uint64_t bs=b[5ULL];if(subtract>0ULL){bs=(1ULL-bs);}
  uint64_t j=0ULL;uint64_t carry=0ULL;uint64_t cmp=magnitude_compare(a,b);
  if(as==bs){while(j<5ULL){uint64_t t=((a[j]+b[j])+carry);out[j]=(t%1000000000ULL);carry=(t/1000000000ULL);j=(j+1ULL);}out[5ULL]=as;}
  else {uint64_t sign=as;if(cmp==0ULL){sign=bs;}
    while(j<5ULL){uint64_t left=a[j];uint64_t right=b[j];if(cmp==0ULL){left=b[j];right=a[j];}
      uint64_t t=(((1000000000ULL+left)-right)-carry);out[j]=(t%1000000000ULL);carry=(1ULL-(t/1000000000ULL));j=(j+1ULL);}
    out[5ULL]=sign;carry=0ULL;}
  canonical_sign(out);return carry;
}
uint64_t fixed_multiply(uint64_t *out,uint64_t *a,uint64_t *b,uint64_t *work) {
  zero_words(work,10ULL);uint64_t i=0ULL;
  while(i<5ULL){uint64_t j=0ULL;uint64_t carry=0ULL;while(j<5ULL){uint64_t k=(i+j);uint64_t t=((work[k]+(a[i]*b[j]))+carry);work[k]=(t%1000000000ULL);carry=(t/1000000000ULL);j=(j+1ULL);}work[(i+5ULL)]=carry;i=(i+1ULL);}
  uint64_t sign=0ULL;if(a[5ULL]!=b[5ULL]){sign=1ULL;}uint64_t lost=0ULL;i=0ULL;while(i<4ULL){lost=(lost+work[i]);i=(i+1ULL);}
  i=0ULL;while(i<5ULL){out[i]=work[(i+4ULL)];i=(i+1ULL);}out[5ULL]=sign;uint64_t overflow=work[9ULL];
  if(sign>0ULL){if(lost>0ULL){overflow=(overflow+increment_words(out,5ULL));}}
  canonical_sign(out);return overflow;
}
uint64_t complex_multiply(uint64_t *out,uint64_t *a,uint64_t *b,uint64_t *work) {
  uint64_t status=0ULL;
  status=(status+fixed_multiply(work,a,b,(work+36ULL)));
  status=(status+fixed_multiply((work+6ULL),(a+6ULL),(b+6ULL),(work+36ULL)));
  status=(status+fixed_multiply((work+12ULL),a,(b+6ULL),(work+36ULL)));
  status=(status+fixed_multiply((work+18ULL),(a+6ULL),b,(work+36ULL)));
  status=(status+fixed_add(out,work,(work+6ULL),1ULL));
  status=(status+fixed_add((out+6ULL),(work+12ULL),(work+18ULL),0ULL));return status;
}
uint64_t initialize_root(uint64_t *root,uint64_t n,uint64_t *work) {
  /* work0..5=x,6..11=x^2,12..17=cos term,18..23=sin term;
     output and multiplication scratch are disjoint. */
  zero_words(work,80ULL);work[0ULL]=279502884ULL;work[1ULL]=462643383ULL;work[2ULL]=589793238ULL;work[3ULL]=141592653ULL;work[4ULL]=3ULL;
  uint64_t status=multiply_small(work,5ULL,2ULL);divide_small(work,5ULL,n,0ULL);
  status=(status+fixed_multiply((work+6ULL),work,work,(work+36ULL)));
  zero_words(root,12ULL);root[4ULL]=1ULL;work[16ULL]=1ULL;copy_words((work+18ULL),work,6ULL);copy_words((root+6ULL),work,6ULL);
  uint64_t i=1ULL;while(i<=10ULL){
    status=(status+fixed_multiply((work+24ULL),(work+12ULL),(work+6ULL),(work+36ULL)));copy_words((work+12ULL),(work+24ULL),6ULL);
    divide_small((work+12ULL),5ULL,((2ULL*i)*((2ULL*i)-1ULL)),0ULL);
    status=(status+fixed_multiply((work+24ULL),(work+18ULL),(work+6ULL),(work+36ULL)));copy_words((work+18ULL),(work+24ULL),6ULL);
    divide_small((work+18ULL),5ULL,((2ULL*i)*((2ULL*i)+1ULL)),0ULL);
    status=(status+fixed_add(root,root,(work+12ULL),(i%2ULL)));
    status=(status+fixed_add((root+6ULL),(root+6ULL),(work+18ULL),(i%2ULL)));i=(i+1ULL);}
  root[11ULL]=1ULL;canonical_sign((root+6ULL));return status;
}
uint64_t magnitude_into(uint64_t *out,uint64_t value) {
  zero_words(out,6ULL);out[0ULL]=(value%1000000000ULL);out[1ULL]=(value/1000000000ULL);return 0ULL;
}
uint64_t add_magnitude(uint64_t *out,uint64_t *a,uint64_t n) {
  uint64_t i=0ULL;uint64_t carry=0ULL;while(i<n){uint64_t x=0ULL;if(i<5ULL){x=a[i];}uint64_t t=((out[i]+x)+carry);out[i]=(t%1000000000ULL);carry=(t/1000000000ULL);i=(i+1ULL);}return carry;
}
uint64_t convert_bound(uint64_t *a,uint64_t n) {
  uint64_t i=2ULL;while(i<n){if(a[i]!=0ULL){return 18446744073709551615ULL;}i=(i+1ULL);}return (a[0ULL]+(1000000000ULL*a[1ULL]));
}
uint64_t w4_norm_upper(uint64_t n) {
  uint64_t *data=(uint64_t *)calloc((n*12ULL),8ULL);uint64_t *twiddle=(uint64_t *)calloc(((n/2ULL)*12ULL),8ULL);
  uint64_t *work=(uint64_t *)calloc(512ULL,8ULL);
  if(data==NULL){return 18446744073709551615ULL;}if(twiddle==NULL){free(data);return 18446744073709551615ULL;}if(work==NULL){free(data);free(twiddle);return 18446744073709551615ULL;}
  zero_words(data,(n*12ULL));zero_words(twiddle,((n/2ULL)*12ULL));zero_words(work,512ULL);
  uint64_t *root=(work+128ULL);uint64_t *temp=(work+160ULL);uint64_t *total=(work+192ULL);uint64_t *quad=(work+208ULL);
  uint64_t status=initialize_root(root,n,work);twiddle[4ULL]=1ULL;uint64_t j=1ULL;
  while(j<(n/2ULL)){status=(status+complex_multiply((twiddle+(j*12ULL)),(twiddle+((j-1ULL)*12ULL)),root,work));j=(j+1ULL);}
  j=0ULL;while(j<2520ULL){uint64_t e=encoded_node(j);uint64_t value=0ULL;uint64_t sign=0ULL;
    if(e>=10000000000000000ULL){value=(e-10000000000000000ULL);}else{value=(10000000000000000ULL-e);sign=1ULL;}
    uint64_t scaled=(value*100ULL);uint64_t *p=(data+(j*12ULL));p[2ULL]=(scaled%1000000000ULL);scaled=(scaled/1000000000ULL);p[3ULL]=(scaled%1000000000ULL);p[4ULL]=(scaled/1000000000ULL);p[5ULL]=sign;canonical_sign(p);
    if(j>0ULL){copy_words((data+((n-j)*12ULL)),p,12ULL);}j=(j+1ULL);}
  uint64_t i=1ULL;j=0ULL;while(i<n){uint64_t bit=(n/2ULL);while(j>=bit){j=(j-bit);bit=(bit/2ULL);}j=(j+bit);
    if(i<j){copy_words(temp,(data+(i*12ULL)),12ULL);copy_words((data+(i*12ULL)),(data+(j*12ULL)),12ULL);copy_words((data+(j*12ULL)),temp,12ULL);}i=(i+1ULL);}
  uint64_t length=2ULL;while(length<=n){uint64_t half=(length/2ULL);uint64_t stride=(n/length);uint64_t block=0ULL;
    while(block<n){j=0ULL;while(j<half){uint64_t *a=(data+((block+j)*12ULL));uint64_t *b=(data+(((block+j)+half)*12ULL));uint64_t *w=(twiddle+((j*stride)*12ULL));
      status=(status+complex_multiply(temp,b,w,work));status=(status+fixed_add((work+48ULL),a,temp,0ULL));status=(status+fixed_add((work+54ULL),(a+6ULL),(temp+6ULL),0ULL));
      status=(status+fixed_add(b,a,temp,1ULL));status=(status+fixed_add((b+6ULL),(a+6ULL),(temp+6ULL),1ULL));copy_words(a,(work+48ULL),12ULL);j=(j+1ULL);}block=(block+length);}length=(length*2ULL);}
  i=0ULL;while(i<n){status=(status+add_magnitude(total,(data+(i*12ULL)),6ULL));i=(i+1ULL);}
  uint64_t lost=(total[0ULL]+total[1ULL]);i=0ULL;while(i<4ULL){total[i]=total[(i+2ULL)];i=(i+1ULL);}total[4ULL]=0ULL;total[5ULL]=0ULL;if(lost>0ULL){status=(status+increment_words(total,6ULL));}
  status=(status+divide_small(total,6ULL,100ULL,1ULL));status=(status+divide_small(total,6ULL,n,1ULL));
  j=0ULL;while(j<2520ULL){uint64_t e=encoded_node(j);uint64_t value=0ULL;if(e>=10000000000000000ULL){value=(e-10000000000000000ULL);}else{value=(10000000000000000ULL-e);}
    magnitude_into(temp,value);status=(status+multiply_small(temp,5ULL,((20ULL*j)*j)));status=(status+add_magnitude(quad,temp,6ULL));j=(j+1ULL);}
  status=(status+divide_small(quad,6ULL,3ULL,1ULL));status=(status+divide_small(quad,6ULL,n,1ULL));status=(status+divide_small(quad,6ULL,n,1ULL));
  uint64_t answer=18446744073709551615ULL;if(status==0ULL){uint64_t first=convert_bound(total,6ULL);uint64_t second=convert_bound(quad,6ULL);if(first<18446744073709551000ULL){if(second<(18446744073709551000ULL-first)){answer=((first+second)+100ULL);}}}
  free(data);free(twiddle);free(work);return answer;
}
int main(void) {printf("%llu\n",(unsigned long long)w4_norm_upper(16777216ULL));return 0;}
