static I gaussianCell(I left,I right,I width){I q=rat(601,2500);
return mul(width,mul(expNeg(mul(q,mul(left,left))),cubeRoot(right)));}
