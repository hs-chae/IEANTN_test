while((i<cells)){I left=pointEdge(h,span,i,cells);
I right=pointEdge(h,span,(i+1),cells);
I c;
I D;
pointHeight(right,(&c),(&D));
(c=add(c,rat(21600,1)));
I fc={(c.hi),(c.hi)};
I fd={(D.hi),(D.hi)};
I w=positiveSub(expNeg(left),expNeg(right));
(total=add(total,mul(mul(rat(2,1),mul(w,fc)),paired(fd,330))));
emitU((c.hi));
emitU((D.hi));
(i=(i+1));}
