/* Exploratory floating evaluator only. No PV or rigorous enclosure is claimed. */
#include <math.h>
#include <stddef.h>

long double trig_value(size_t n, const double *w, long double y) {
    const long double t = cosl(2.0L * acosl(-1.0L) * y);
    long double a = 0.0L, b = 0.0L;
    for (size_t j = n; j-- > 1;) {
        long double c = 2.0L * t * a - b + 2.0L * (long double)w[j];
        b = a;
        a = c;
    }
    return (long double)w[0] + t * a - b;
}

long double trig_primitive(size_t n, const double *w, long double y) {
    const long double pi = acosl(-1.0L), theta = 2.0L * pi * y;
    const long double t = cosl(theta);
    long double a = 0.0L, b = sinl(theta), sum = 0.0L, correction = 0.0L;
    for (size_t j = 1; j < n; ++j) {
        long double term = (long double)w[j] * b / (pi * (long double)j);
        long double next = term - correction, total = sum + next;
        correction = (total - sum) - next;
        sum = total;
        long double c = 2.0L * t * b - a;
        a = b;
        b = c;
    }
    return (long double)w[0] * y + sum;
}
