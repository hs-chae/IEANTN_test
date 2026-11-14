static I runRow(Row row,unsigned int mark,unsigned int limit){I acc=izero();
lean_inc(((acc.lo).mag));
lean_inc(((acc.hi).mag));
unsigned int i=0;
unsigned int cells=(row.cells);
if(((limit>0)&&(limit<cells)))(cells=limit);else ;
if((cells==0))(cells=1);else ;
while((i<cells)){I next=iadd(acc,evaluate((row.nodes),(row.count),i));
lean_inc(((next.lo).mag));
lean_inc(((next.hi).mag));
clearTo(mark);
lean_dec(((acc.lo).mag));
lean_dec(((acc.hi).mag));
(acc=next);
(i=(i+1));}
return acc;}
