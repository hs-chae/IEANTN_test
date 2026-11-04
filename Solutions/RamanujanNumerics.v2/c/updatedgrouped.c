double sum(const double *a, unsigned n) {
    double s = 0.0;
    for (unsigned i = 0; i < n; ++i) {
        s += a[i];
    }
    return s;
}

static const double inputs[1] = {
    0.06398942665601896340188403655702131800353527069091796875
};
double ramanujan_epsilon_bound(void) {
    double s = sum(inputs, 1);
    double r = (s * 4096.0);
    r = (r - 134.0);
    r = (r - 119.0);
    return r;
}
