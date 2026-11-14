int main(){lean_initialize_runtime_module();
for(unsigned int j=0;(j<52);(j=(j+1))){prepare((allDepths[j]));
unsigned int mark=poolTop;
I result=runRow((allRows[j]),mark,0);
printI(result);
clearTo(mark);
lean_dec(((result.lo).mag));
lean_dec(((result.hi).mag));
clearTo(0);}
fprintf(stderr,"poolHigh=%u\n",poolHigh);
return 0;}
