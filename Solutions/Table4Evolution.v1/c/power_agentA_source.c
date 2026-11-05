double sum(const double *a, unsigned n) {
    double s = 0.0;
    for (unsigned i = 0; i < n; ++i) {
        s += a[i];
    }
    return s;
}

static const double inputs[2] = {
    0.63385600006400000250295079240459017455577850341796875,
    0.002212025824686791354578563328914242447353899478912353515625
};
double fks2_power_transport(void) {
    double s = sum(inputs, 2);
    double r = (s * 0.015625);
    r = (r + 0.000000143740122934836231559049303518893481168561265803873538970947265625);
    return r;
}
