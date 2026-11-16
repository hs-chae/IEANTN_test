static I expPositive(I x){if(((x.lo)>(x.hi)))fail();else ;
I left={(x.lo),(x.lo)};
I right={(x.hi),(x.hi)};
I lower=expPositiveRaw(left);
I upper=expPositiveRaw(right);
I out={(lower.lo),(upper.hi)};
return out;}
