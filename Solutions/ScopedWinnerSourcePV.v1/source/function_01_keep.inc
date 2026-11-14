static N keep(N x){if((poolTop>=4000000))fail();else ;
((pool[poolTop])=x);
(poolTop=(poolTop+1));
if((poolHigh<poolTop))(poolHigh=poolTop);else ;
return x;}
