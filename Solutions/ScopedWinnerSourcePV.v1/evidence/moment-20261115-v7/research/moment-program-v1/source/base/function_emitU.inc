static void emitU(U x){uint64_t words[8];
unsigned int i=0;
while((i<8)){((words[i])=((uint64_t)(x>>(64*i))));
(i=(i+1));}
if((fwrite(words,8,8,stdout)!=8))fail();else ;}
