#include <stdint.h>
#include <stdio.h>
#include <limits.h>
#include "verified_finite_cell.c"
_Static_assert(CHAR_BIT==8 && sizeof(uint64_t)==8, "specified input ABI");
int main(int argc,char **argv) {
  uint64_t header[2]={rpc_e_low(),rpc_e_high()};
  if(argc!=65 || fwrite(header,8,2,stdout)!=2) return 2;
  uint64_t total=0;
  for(int file=1;file<argc;++file) {
    FILE *input=fopen(argv[file],"rb"); if(!input) return 3;
    uint64_t row[7]; size_t got;
    while((got=fread(row,8,7,input))!=0) {
      if(got!=7 || rpc_finite_cell(row[0],row[1],row[2],row[3],row[4],row[5],row[6])!=1) {
        fprintf(stderr,"scalar failure at record %llu\n",(unsigned long long)total); return 4;
      }
      uint64_t logarithm=rpc_log_upper(row[0]);
      if(fwrite(&logarithm,8,1,stdout)!=1) return 5;
      ++total;
    }
    if(ferror(input) || fclose(input)!=0) return 6;
  }
  if(total!=1755663 || fflush(stdout)!=0) return 7;
  fprintf(stderr,"processed=%llu\n",(unsigned long long)total);
  return 0;
}
