#!/usr/bin/env python3
"""Separate candidate recursive C port; equivalence proof remains pending."""
from pathlib import Path
H=Path(__file__).resolve().parent
s=(H/'fft_body.c').read_text();pos=s.index('uint64_t w4_norm_upper');s=s[:pos]+(H/'recursive_kernel.c').read_text()+s[pos:]
s=s.replace('uint64_t w4_norm_upper(uint64_t n)', 'uint64_t w4_recursive_norm_upper(uint64_t n)')
s=s.replace('  uint64_t *work=(uint64_t *)calloc(512ULL,8ULL);','  uint64_t *work=(uint64_t *)calloc(512ULL,8ULL);uint64_t *output=(uint64_t *)calloc((n*12ULL),8ULL);')
needle='  zero_words(data,(n*12ULL));';s=s.replace(needle,'  if(output==NULL){free(data);free(twiddle);free(work);return 18446744073709551615ULL;}\n  zero_words(output,(n*12ULL));\n'+needle)
a=s.index('  uint64_t i=1ULL;j=0ULL;');b=s.index('  i=0ULL;while(i<n)',a)
s=s[:a]+'  status=(status+fft_recursive(output,0ULL,data,0ULL,1ULL,twiddle,n,n,work));\n  uint64_t i=0ULL;\n'+s[b:]
s=s.replace('add_magnitude(total,(data+(i*12ULL)),6ULL)','add_magnitude(total,(output+(i*12ULL)),6ULL)')
s=s.replace('free(data);free(twiddle);free(work);return answer;','free(data);free(twiddle);free(work);free(output);return answer;')
s=s.replace('w4_norm_upper(16777216ULL)','w4_recursive_norm_upper(16777216ULL)')
old=(H.parent/'window_scalars.c').read_text();a=old.index('uint64_t encoded_node');b=old.index('uint64_t positive_part',a)
(H/'w4_fft_recursive.c').write_text('/* Separate recursive FFT source port; verification incomplete. */\n#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n'+old[a:b]+s)
