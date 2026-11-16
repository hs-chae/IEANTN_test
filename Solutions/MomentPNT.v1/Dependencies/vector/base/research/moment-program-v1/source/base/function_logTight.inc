static I logTight(I x){if((((x.lo)<S)||((x.lo)>(x.hi))))fail();else ;
I left={(x.lo),(x.lo)};
I right={(x.hi),(x.hi)};
I lower=logPos(left);
I upper=logPos(right);
I out={(lower.lo),(upper.hi)};
return out;}
