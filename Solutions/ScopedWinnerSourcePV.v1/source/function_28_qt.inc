static Q qt(Q a,Q b){N g=ng(((a.num).mag),(b.den));
N h=ng(((b.num).mag),(a.den));
S top=sm(smake(nd(((a.num).mag),g),((a.num).neg)),smake(nd(((b.num).mag),h),((b.num).neg)));
Q r={top,nm(nd((a.den),h),nd((b.den),g))};
return r;}
