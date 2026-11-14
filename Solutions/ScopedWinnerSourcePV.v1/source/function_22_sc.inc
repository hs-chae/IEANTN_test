static int sc(S a,S b){if(((a.neg)!=(b.neg)))return ((a.neg)?(-1):1);else ;
if(ne((a.mag),(b.mag)))return 0;else ;
if(nlt((a.mag),(b.mag)))return ((a.neg)?1:(-1));else ;
return ((a.neg)?(-1):1);}
