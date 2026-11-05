double sum(const double *a, unsigned n) {
    double s = 0.0;
    for (unsigned i = 0; i < n; ++i) {
        s += a[i];
    }
    return s;
}

static const double inputs[2] = {
    0.6260480000640000763922898840974085032939910888671875,
    0.00218477752596056562506277032298385165631771087646484375
};
double fks2_power_transport(void) {
    double s = sum(inputs, 2);
    double r = (s * 0.015625);
    r = (r + 0.000000143740122400859461829886708217340895998859195969998836517333984375);
    return r;
}
