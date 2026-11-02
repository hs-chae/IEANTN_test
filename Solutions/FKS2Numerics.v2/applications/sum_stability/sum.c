double sum(const double *a, unsigned n) {
    double s = 0.0;
    for (unsigned i = 0; i < n; ++i) {
        s += a[i];
    }
    return s;
}
