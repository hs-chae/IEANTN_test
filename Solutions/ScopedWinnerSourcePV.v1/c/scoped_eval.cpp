// Exact application arithmetic. Generic Nat operations/RC come only from the
// pinned Lean core runtime; no application evaluator is called through that ABI.
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
extern "C" void lean_initialize_runtime_module(void);

typedef lean_object *N;
struct S { N mag; unsigned neg; };
struct Q { S num; N den; };
struct RI { Q lo; Q hi; };
struct I { S lo; S hi; unsigned ok; };
struct Node { unsigned op; unsigned a; unsigned b; const char *num; const char *den; };
struct Row { const Node *nodes; unsigned count; unsigned cells; };

// Each slot owns one runtime reference, including repeated/scalar results.
// Borrowed Q/I fields remain valid until the pool is cleared. Persistent row
// accumulators explicitly retain their references across that clear operation.
static N pool[4000000];
static unsigned poolTop = 0;
static unsigned poolHigh = 0;
static unsigned depth = 24;
static N scale100;
static Q expCoeffs[65];
static Q atanhCoeffs[65];
static RI preparedLn2;

static void fail(void) { fputs("scoped evaluator domain/resource failure\n", stderr); exit(3); }
static N keep(N x) {
    if (poolTop >= 4000000) fail();
    pool[poolTop] = x;
    poolTop = poolTop + 1;
    if (poolHigh < poolTop) poolHigh = poolTop;
    return x;
}
static void clearTo(unsigned mark) {
    if (mark > poolTop) fail();
    while (poolTop > mark) { poolTop = poolTop - 1; lean_dec(pool[poolTop]); }
}
static N nu(unsigned a) { return keep(lean_unsigned_to_nat(a)); }
static N na(N a,N b) { return keep(lean_nat_add(a,b)); }
static N ns(N a,N b) { return keep(lean_nat_sub(a,b)); }
static N nm(N a,N b) { return keep(lean_nat_mul(a,b)); }
static N nd(N a,N b) { return keep(lean_nat_div(a,b)); }
static N nr(N a,N b) { return keep(lean_nat_mod(a,b)); }
static N ng(N a,N b) { return keep(lean_nat_gcd(a,b)); }
static N nl(N a,N b) { return keep(lean_nat_shiftl(a,b)); }
static unsigned ne(N a,N b) { return (unsigned)lean_nat_dec_eq(a,b); }
static unsigned nle(N a,N b) { return (unsigned)lean_nat_dec_le(a,b); }
static unsigned nlt(N a,N b) { return (unsigned)lean_nat_dec_lt(a,b); }
static unsigned nz(N a) { return ne(a,nu(0)); }
static unsigned small(N a) {
    if (!nle(a,nu(4294967295u))) fail();
    return (unsigned)lean_unbox(a);
}
static N decimal(const char *s) {
    N a = nu(0);
    unsigned k = 0;
    while (s[k] != 0) {
        if (s[k] < '0' || s[k] > '9') fail();
        a = na(nm(a,nu(10)),nu((unsigned)(s[k]-'0')));
        k = k + 1;
    }
    return a;
}
static S smake(N mag,unsigned neg) { S r = {mag,nz(mag) ? 0u : neg}; return r; }
static S si(unsigned n) { return smake(nu(n),0); }
static S sn(S a) { return smake(a.mag,1-a.neg); }
static S sa(S a,S b) {
    if (a.neg == b.neg) return smake(na(a.mag,b.mag),a.neg);
    if (nle(b.mag,a.mag)) return smake(ns(a.mag,b.mag),a.neg);
    return smake(ns(b.mag,a.mag),b.neg);
}
static S sm(S a,S b) { return smake(nm(a.mag,b.mag),(a.neg+b.neg)%2); }
static int sc(S a,S b) {
    if (a.neg != b.neg) return a.neg ? -1 : 1;
    if (ne(a.mag,b.mag)) return 0;
    if (nlt(a.mag,b.mag)) return a.neg ? 1 : -1;
    return a.neg ? -1 : 1;
}
static Q qm(S a,N b) {
    if (nz(b)) fail();
    N g = ng(a.mag,b);
    Q r = {smake(nd(a.mag,g),a.neg),nd(b,g)};
    return r;
}
static Q qi(unsigned n) { Q r = {si(n),nu(1)}; return r; }
static Q qn(Q a) { Q r = {sn(a.num),a.den}; return r; }
static Q qa(Q a,Q b) {
    S an = sm(a.num,smake(b.den,0));
    S bn = sm(b.num,smake(a.den,0));
    return qm(sa(an,bn),nm(a.den,b.den));
}
static Q qs(Q a,Q b) { return qa(a,qn(b)); }
static Q qt(Q a,Q b) {
    N g = ng(a.num.mag,b.den);
    N h = ng(b.num.mag,a.den);
    S top = sm(smake(nd(a.num.mag,g),a.num.neg),smake(nd(b.num.mag,h),b.num.neg));
    Q r = {top,nm(nd(a.den,h),nd(b.den,g))};
    return r;
}
static Q qv(Q a,Q b) {
    if (nz(b.num.mag)) return qi(0);
    Q inverse = {smake(b.den,b.num.neg),b.num.mag};
    return qt(a,inverse);
}
static int qc(Q a,Q b) { return sc(sm(a.num,smake(b.den,0)),sm(b.num,smake(a.den,0))); }
static Q qabs(Q a) { Q r = {smake(a.num.mag,0),a.den}; return r; }
static Q qmin(Q a,Q b) { return qc(a,b) <= 0 ? a : b; }
static Q qmax(Q a,Q b) { return qc(a,b) <= 0 ? b : a; }
static Q qpow(Q a,unsigned n) {
    Q result = qi(1);
    while (n > 0) {
        if (n%2 == 1) result = qt(result,a);
        n = n/2;
        if (n > 0) a = qt(a,a);
    }
    return result;
}
static S floorQ(Q q) {
    N a = nd(q.num.mag,q.den);
    if (q.num.neg && !nz(nr(q.num.mag,q.den))) a = na(a,nu(1));
    return smake(a,q.num.neg);
}
static S ceilQ(Q q) { return sn(floorQ(qn(q))); }
static RI point(Q q) { RI r = {q,q}; return r; }
static RI radd(RI a,RI b) { RI r = {qa(a.lo,b.lo),qa(a.hi,b.hi)}; return r; }
static RI rneg(RI a) { RI r = {qn(a.hi),qn(a.lo)}; return r; }
static RI rmul(RI a,RI b) {
    Q p = qt(a.lo,b.lo); Q q = qt(a.lo,b.hi);
    Q r = qt(a.hi,b.lo); Q s = qt(a.hi,b.hi);
    RI out = {qmin(qmin(p,q),qmin(r,s)),qmax(qmax(p,q),qmax(r,s))};
    return out;
}
static RI rhull(RI a,RI b) { RI r = {qmin(a.lo,b.lo),qmax(a.hi,b.hi)}; return r; }
static RI rpow(RI a,unsigned n) {
    if (n == 0) return point(qi(1));
    unsigned bit = 1;
    while (bit <= n/2) bit = bit*2;
    RI result = a;
    bit = bit/2;
    while (bit > 0) {
        result = rmul(result,result);
        if ((n/bit)%2 == 1) result = rmul(a,result);
        bit = bit/2;
    }
    return result;
}
static RI taylor(const Q *coeffs,RI a) {
    RI result = point(qi(0));
    unsigned k = depth+1;
    while (k > 0) { k = k-1; result = radd(point(coeffs[k]),rmul(result,a)); }
    return result;
}
static RI expRemainder(RI a) {
    Q r = qmax(qabs(a.lo),qabs(a.hi));
    S ceil = ceilQ(r);
    if (ceil.neg) fail();
    unsigned c = small(ceil.mag);
    if (c == 4294967295u) fail();
    Q fact = qi(1);
    unsigned k = 1;
    while (k <= depth+1) { fact = qt(fact,qi(k)); k = k+1; }
    Q error = qv(qt(qpow(qi(3),c+1),qpow(r,depth+1)),fact);
    RI out = {qn(error),error}; return out;
}
static RI expPoint(Q q) {
    S ceil = ceilQ(qabs(q));
    N m = na(ceil.mag,nu(1));
    unsigned k = small(keep(lean_nat_log2(m)));
    if (k >= 32) fail();
    unsigned power = 1u << k;
    Q reduced = qv(q,qi(power));
    RI input = point(reduced);
    return rpow(radd(taylor(expCoeffs,input),expRemainder(input)),power);
}
static RI rexp(RI a) {
    if (qc(a.hi,qi(0)) <= 0 || qc(qi(0),a.lo) <= 0)
        return rhull(expPoint(a.lo),expPoint(a.hi));
    return radd(taylor(expCoeffs,a),expRemainder(a));
}
static RI atanhPoint(Q q) {
    Q r = qabs(q);
    if (qc(r,qi(1)) >= 0) { RI wide = {qn(qi(1000)),qi(1000)}; return wide; }
    Q error = qv(qpow(r,depth+1),qs(qi(1),r));
    RI remainder = {qn(error),error};
    return radd(taylor(atanhCoeffs,point(q)),remainder);
}
static RI logPoint(Q q) {
    if (qc(q,qi(0)) <= 0) { RI wide = {qn(qi(1000)),qi(1000)}; return wide; }
    unsigned a = small(keep(lean_nat_log2(q.num.mag)));
    unsigned b = small(keep(lean_nat_log2(q.den)));
    if (a > 2147483647u || b > 2147483647u) fail();
    int k = (int)a-(int)b;
    Q m = q;
    if (k >= 0) m = qv(q,qpow(qi(2),(unsigned)k));
    else m = qt(q,qpow(qi(2),(unsigned)(-k)));
    Q y = qv(qs(m,qi(1)),qa(m,qi(1)));
    Q factor = qi((unsigned)(k < 0 ? -k : k));
    if (k < 0) factor = qn(factor);
    return radd(rmul(point(qi(2)),atanhPoint(y)),rmul(point(factor),preparedLn2));
}
static RI rlog(RI a) {
    if (qc(a.lo,qi(0)) <= 0) { RI wide = {qn(qi(1000)),qi(1000)}; return wide; }
    return rhull(logPoint(a.lo),logPoint(a.hi));
}
static Q fromS(S a) { return qm(a,scale100); }
static I fromRI(RI a,unsigned ok) {
    Q factor = {smake(scale100,0),nu(1)};
    I out = {floorQ(qt(a.lo,factor)),ceilQ(qt(a.hi,factor)),ok}; return out;
}
static RI toRI(I a) { RI r = {fromS(a.lo),fromS(a.hi)}; return r; }
static I izero(void) { I r = {si(0),si(0),1}; return r; }
static I iconst(Q q) { return fromRI(point(q),1); }
static I iadd(I a,I b) { I r = {sa(a.lo,b.lo),sa(a.hi,b.hi),a.ok && b.ok}; return r; }
static I imul(I a,I b) { return fromRI(rmul(toRI(a),toRI(b)),a.ok && b.ok); }
static I ineg(I a) { I r = {sn(a.hi),sn(a.lo),a.ok}; return r; }
static I iinv(I a) {
    RI q = toRI(a);
    unsigned valid = qc(q.lo,qi(0)) > 0 || qc(q.hi,qi(0)) < 0;
    if (!valid) {
        Q wide = qm(smake(decimal("1000000000000000000000000000000"),0),nu(1));
        RI r = {qn(wide),wide}; return fromRI(r,0);
    }
    Q l = qv(qi(1),q.hi); Q h = qv(qi(1),q.lo);
    RI r = {qmin(l,h),qmax(l,h)}; return fromRI(r,a.ok);
}
static I iexp(I a) { return fromRI(rexp(toRI(a)),a.ok); }
static I ilog(I a) {
    RI r = toRI(a);
    return fromRI(rlog(r),a.ok && qc(r.lo,qi(0)) > 0);
}
static I named(unsigned c) {
    RI r;
    if (c == 0) {
        r.lo = qm(smake(decimal("31415926535897932"),0),decimal("10000000000000000"));
        r.hi = qm(smake(decimal("31415926535897933"),0),decimal("10000000000000000"));
    } else {
        r.lo = qv(qi(5722),qi(10000)); r.hi = qv(qi(5823),qi(10000));
    }
    return fromRI(r,1);
}
static void prepare(unsigned d) {
    if (d > 64) fail();
    depth = d;
    scale100 = nl(nu(1),nu(100));
    expCoeffs[0] = qi(1);
    atanhCoeffs[0] = qi(0);
    unsigned k = 1;
    while (k <= depth) {
        expCoeffs[k] = qv(expCoeffs[k-1],qi(k));
        atanhCoeffs[k] = k%2 == 1 ? qv(qi(1),qi(k)) : qi(0);
        k = k+1;
    }
    preparedLn2 = rmul(point(qi(2)),atanhPoint(qv(qi(1),qi(3))));
}
static I evaluate(const Node *nodes,unsigned count,unsigned index) {
    I values[8192];
    if (count == 0 || count > 8192) fail();
    unsigned k = 0;
    while (k < count) {
        Node n = nodes[k];
        if (n.op == 0) {
            unsigned negative = n.num[0] == '-';
            N mag = decimal(n.num+negative);
            values[k] = iconst(qm(smake(mag,negative),decimal(n.den)));
        } else if (n.op == 1) values[k] = iconst(qi(index));
        else if (n.op == 8) values[k] = named(n.a);
        else {
            if (n.a >= k) fail();
            I a = values[n.a];
            if (n.op == 2 || n.op == 3) {
                if (n.b >= k) fail();
                if (n.op == 2) values[k] = iadd(a,values[n.b]);
                else values[k] = imul(a,values[n.b]);
            } else if (n.op == 4) values[k] = ineg(a);
            else if (n.op == 5) values[k] = iinv(a);
            else if (n.op == 6) values[k] = iexp(a);
            else if (n.op == 7) values[k] = ilog(a);
            else fail();
        }
        k = k+1;
    }
    return values[count-1];
}
static void printS(S a) {
    char digits[1024]; unsigned count = 0;
    if (a.neg) putchar('-');
    N x = a.mag;
    unsigned first = 1;
    while (first || !nz(x)) {
        first = 0;
        if (count >= 1024) fail();
        digits[count] = (char)('0'+small(nr(x,nu(10))));
        count = count+1; x = nd(x,nu(10));
    }
    while (count > 0) { count = count-1; putchar(digits[count]); }
}
static void printI(I a) {
    printS(a.lo); printf(",-100,"); printS(a.hi); printf(",-100,%u\n",a.ok);
}
static I runRow(Row row,unsigned mark,unsigned limit) {
    I acc = izero(); lean_inc(acc.lo.mag); lean_inc(acc.hi.mag);
    unsigned i = 0;
    unsigned cells = row.cells;
    if (limit > 0 && limit < cells) cells = limit;
    if (cells == 0) cells = 1; // matches Nat subtraction in cells-1
    while (i < cells) {
        I next = iadd(acc,evaluate(row.nodes,row.count,i));
        lean_inc(next.lo.mag); lean_inc(next.hi.mag);
        clearTo(mark); lean_dec(acc.lo.mag); lean_dec(acc.hi.mag); acc = next;
        i = i+1;
    }
    return acc;
}

#include "height_input.inc"

int main(void) {
    lean_initialize_runtime_module();
    prepare(24);
    unsigned mark = poolTop;
    for (unsigned j = 0; j < 4; j = j+1) {
        I result = runRow(heightRows[j],mark,0);
        printI(result); clearTo(mark); lean_dec(result.lo.mag); lean_dec(result.hi.mag);
    }
    fprintf(stderr,"poolHigh=%u\n",poolHigh);
    clearTo(0);
    return 0;
}
