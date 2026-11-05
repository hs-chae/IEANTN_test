double sum(const double *a, unsigned n) {
    double s = 0.0;
    for (unsigned i = 0; i < n; ++i) {
        s += a[i];
    }
    return s;
}

static const double inputs[2] = {
    0.8390400000000000080291329140891321003437042236328125,
    0.002928075379514919092394098498743915115483105182647705078125
};
double fks2_power_transport(void) {
    double s = sum(inputs, 2);
    double r = (s * 0.015625);
    r = (r + 0.00000014374013696704550425669428236064018022943855612538754940032958984375);
    return r;
}
