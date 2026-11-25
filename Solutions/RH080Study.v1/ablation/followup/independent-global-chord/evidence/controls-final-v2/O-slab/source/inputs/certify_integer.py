"""Independent Fourier certificate using only exact Python integer arithmetic."""
import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path

UNIT = 10**30
PI_CENTER = Fraction("3.141592653589793238462643383279502884197")


def arctan_bounds(q, terms):
    result = sum(Fraction((-1)**j, (2*j+1)*q**(2*j+1)) for j in range(terms))
    next_sum = result + Fraction((-1)**terms, (2*terms+1)*q**(2*terms+1))
    return min(result, next_sum), max(result, next_sum)


def initial_root(length):
    a_lo, a_hi = arctan_bounds(5, 40)
    b_lo, b_hi = arctan_bounds(239, 40)
    pi_lo, pi_hi = 16*a_lo - 4*b_hi, 16*a_hi - 4*b_lo
    pi_error = max(abs(pi_lo-PI_CENTER), abs(pi_hi-PI_CENTER))
    if not (pi_hi**2 < 10 and 2*pi_error/length < Fraction(1, 10*UNIT)):
        raise ArithmeticError("Insufficient pi precision")

    angle = 2*PI_CENTER/length
    cos = sum((-1)**i * angle**(2*i) / factorial(2*i) for i in range(10))
    sin = sum((-1)**i * angle**(2*i+1) / factorial(2*i+1) for i in range(10))
    if not angle**20/factorial(20) < Fraction(1, 10*UNIT):
        raise ArithmeticError("Insufficient trigonometric precision")
    return int(cos*UNIT), -int(sin*UNIT)


def twiddles(length):
    c, s = initial_root(length)
    cos, sin = [UNIT], [0]
    for _ in range(1, length//2):
        u, v = cos[-1], sin[-1]
        cos.append((c*u - s*v)//UNIT)
        sin.append((s*u + c*v)//UNIT)
    return cos, sin


def real_dft(values, length):
    cosine, sine = twiddles(length)
    real = [0]*length
    imag = [0]*length
    real[0] = values[0]
    for j, value in enumerate(values[1:], 1):
        real[j] = real[-j] = value

    j = 0
    for i in range(1, length):
        bit = length >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            real[i], real[j] = real[j], real[i]

    width = 2
    while width <= length:
        half = width//2
        stride = length//width
        for start in range(0, length, width):
            for n in range(half):
                i, j = start+n, start+n+half
                u, v = real[j], imag[j]
                c, s = cosine[n*stride], sine[n*stride]
                q, r = (u*c-v*s)//UNIT, (u*s+v*c)//UNIT
                real[i], real[j] = real[i]+q, real[i]-q
                imag[i], imag[j] = imag[i]+r, imag[i]-r
        width *= 2
    return real


def positive_area(left, right):
    if left >= 0 and right >= 0:
        return (left+right)/2
    if left <= 0 and right <= 0:
        return Fraction(0)
    return max(left,right)**2/(2*abs(left-right))


def upper_decimal(x, digits=12):
    scale = 10**digits
    value = -((-x.numerator*scale)//x.denominator)
    return f"{value//scale}.{value%scale:0{digits}d}"


def verify(path, length):
    data = json.loads(path.read_text())
    values, scale, m = data["coefficients"], data["scale"], data["m"]
    if not (scale > 0 and UNIT % scale == 0 and 1 <= m < len(values)):
        raise ValueError("Invalid rational coefficients or grid")
    if not (length >= 2*len(values) and length & (length-1) == 0):
        raise ValueError("Use a sufficiently large power-of-two sample grid")
    stages = length.bit_length()-1

    twiddle_error = Fraction(12*length, UNIT)
    if not (Fraction(4*length,UNIT) < Fraction(1,2) and
            stages*twiddle_error/2 < Fraction(1,2)):
        raise ArithmeticError("Fixed point too coarse for this grid")

    a = [Fraction(x,scale) for x in values]
    fft_values = real_dft([x*(UNIT//scale) for x in values],length)
    trapezoid = Fraction(sum(abs(x) for x in fft_values), length*UNIT)
    amplitude = 2*sum(abs(x) for x in a) - abs(a[0])
    fft_error = 2*length*(twiddle_error*amplitude + Fraction(2,UNIT))
    integration_error = Fraction(80,12*length**2)*sum(j*j*abs(v) for j,v in enumerate(a))
    norm_bound = trapezoid + fft_error + integration_error

    positive_tail = 2*sum(positive_area(a[j],a[j+1] if j+1 < len(a) else Fraction(0))
                          for j in range(m,len(a)))/m
    denominator = (2*sum(a)-a[0])/m - Fraction(data["A"])*positive_tail
    goal = Fraction(data["threshold"])
    if denominator <= 0 or not norm_bound < goal*denominator:
        raise ArithmeticError("Certificate failed")
    return dict(file=path.name, threshold=str(goal), grid_size=length,
                ratio_upper_bound=upper_decimal(norm_bound/denominator),
                fft_error_upper=upper_decimal(fft_error,24),
                integration_error_upper=upper_decimal(integration_error,18),
                margin_lower=str(goal*denominator-norm_bound))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("witnesses", type=Path, nargs="+")
    parser.add_argument("--grid-size", type=int, default=2**17)
    args = parser.parse_args()
    print(json.dumps([verify(path,args.grid_size) for path in args.witnesses], indent=2))
