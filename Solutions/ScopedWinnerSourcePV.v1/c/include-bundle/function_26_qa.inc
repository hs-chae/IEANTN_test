static Q qa(Q a,Q b){S an=sm((a.num),smake((b.den),0));
S bn=sm((b.num),smake((a.den),0));
return qm(sa(an,bn),nm((a.den),(b.den)));}
