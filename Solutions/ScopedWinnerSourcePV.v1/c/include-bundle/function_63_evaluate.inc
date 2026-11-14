static I evaluate(const Node* nodes,unsigned int count,unsigned int index){I values[8192];
if(((count==0)||(count>8192)))fail();else ;
unsigned int k=0;
while((k<count)){Node n=(nodes[k]);
if(((n.op)==0)){unsigned int negative=(((n.num)[0])=='-');
N mag=decimal(((n.num)+negative));
((values[k])=iconst(qm(smake(mag,negative),decimal((n.den)))));}else if(((n.op)==1))((values[k])=iconst(qi(index)));else if(((n.op)==8))((values[k])=named((n.a)));else {if(((n.a)>=k))fail();else ;
I a=(values[(n.a)]);
if((((n.op)==2)||((n.op)==3))){if(((n.b)>=k))fail();else ;
if(((n.op)==2))((values[k])=iadd(a,(values[(n.b)])));else ((values[k])=imul(a,(values[(n.b)])));}else if(((n.op)==4))((values[k])=ineg(a));else if(((n.op)==5))((values[k])=iinv(a));else if(((n.op)==6))((values[k])=iexp(a));else if(((n.op)==7))((values[k])=ilog(a));else fail();}
(k=(k+1));}
return (values[(count-1)]);}
