static double exp_small(double x) {
    double y = (x / 32.0);
    double term = 1.0;
    double sum = 1.0;
    for (double n = 1.0; n <= 18.0; n = (n + 1.0)) {
        term = ((term * y) / n);
        sum = (sum + term);
    }
    for (double n = 0.0; n < 5.0; n = (n + 1.0)) {
        sum = (sum * sum);
    }
    return sum;
}

static double sqrt_fixed(double x) {
    double y = 3.0;
    for (double n = 0.0; n < 5.0; n = (n + 1.0)) {
        y = (0.5 * (y + (x / y)));
    }
    return y;
}

double fks2_value(void) {
    double r = 5.5666305;
    double a1 = (1.0 + 0.0000000193378);
    double log2 = 0.6931471805599453;
    double s1 = 0.0;
    double s2 = 0.0;
    for (double k = 3.0; k <= 43.0; k = (k + 1.0)) {
        double t = (30.0 * ((1.0 / k) - (1.0 / 3.0)));
        s1 = (s1 + exp_small(t));
    }
    for (double k = 3.0; k <= 44.0; k = (k + 1.0)) {
        double t = ((44.0 * log2) * ((1.0 / k) - (1.0 / 3.0)));
        s2 = (s2 + exp_small(t));
    }
    double a2 = s1;
    if (s1 < s2) {
        a2 = s2;
    }
    a2 = (a1 * a2);
    double u = (r / 30.0);
    double z = sqrt_fixed((30.0 / r));
    double p = (((1.0 / 121.096) * u) / z);
    p = (p * exp_small((2.0 * z)));
    double b1 = ((a1 * 30.0) * exp_small((-15.0)));
    double b2 = ((a2 * 30.0) * exp_small((-20.0)));
    return (p * (b1 + b2));
}
