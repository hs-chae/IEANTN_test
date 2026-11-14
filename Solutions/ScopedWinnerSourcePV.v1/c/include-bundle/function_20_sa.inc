static S sa(S a,S b){if(((a.neg)==(b.neg)))return smake(na((a.mag),(b.mag)),(a.neg));else ;
if(nle((b.mag),(a.mag)))return smake(ns((a.mag),(b.mag)),(a.neg));else ;
return smake(ns((b.mag),(a.mag)),(b.neg));}
