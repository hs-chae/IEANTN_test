uint64_t fft_recursive(uint64_t *output,uint64_t start,uint64_t *input,uint64_t index,uint64_t step,uint64_t *twiddle,uint64_t n,uint64_t total,uint64_t *work) {
  if(n==1ULL){copy_words((output+(start*12ULL)),(input+(index*12ULL)),12ULL);return 0ULL;}
  uint64_t half=(n/2ULL);uint64_t status=fft_recursive(output,start,input,index,(step*2ULL),twiddle,half,total,work);
  status=(status+fft_recursive(output,(start+half),input,(index+step),(step*2ULL),twiddle,half,total,work));
  uint64_t stride=(total/n);uint64_t j=0ULL;uint64_t *temp=(work+160ULL);
  while(j<half){uint64_t *a=(output+((start+j)*12ULL));uint64_t *b=(output+(((start+j)+half)*12ULL));uint64_t *w=(twiddle+((j*stride)*12ULL));
    status=(status+complex_multiply(temp,b,w,work));status=(status+fixed_add((work+48ULL),a,temp,0ULL));status=(status+fixed_add((work+54ULL),(a+6ULL),(temp+6ULL),0ULL));
    status=(status+fixed_add(b,a,temp,1ULL));status=(status+fixed_add((b+6ULL),(a+6ULL),(temp+6ULL),1ULL));copy_words(a,(work+48ULL),12ULL);j=(j+1ULL);}
  return status;
}
