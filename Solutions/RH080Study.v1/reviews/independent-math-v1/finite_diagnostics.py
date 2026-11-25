#!/usr/bin/env python3
"""Independent finite arithmetic checks and actual compiled-C comparison.

These diagnostics support review; they are not a source-first proof.
"""
import ctypes, hashlib, json, math, pathlib, subprocess
from fractions import Fraction as Q

HERE = pathlib.Path(__file__).resolve().parent
STUDY = HERE.parents[1]
SOURCE = STUDY/'pv/dual_grid.c'
LIMIT = 2**64
largest = 0

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def checked(x):
    global largest
    need(0 <= x < LIMIT, 'u64 diagnostic overflow/underflow')
    largest = max(largest, x)
    return x

def sine(r):
    z = checked(3141592654*r)//256
    term, positive, negative = z, z, 0
    for n in range(1, 9):
        term = checked(checked(term*z)//10**9*z)//10**9
        term //= checked(checked(2*n)*checked(2*n+1))
        if n%2 == 0:
            positive = checked(positive+term)
        else:
            negative = checked(negative+term)
    return checked(positive-negative)

positive = {4:837, 7:251, 9:249, 11:176, 15:111, 17:82, 19:18}
negative = {5:621, 6:129, 8:229, 10:170, 12:119, 13:23, 14:15, 16:103, 18:59}
heights = [256,256,256,256,-581,40,169,-82,147,-102,68,-108,11,34,49,-62,41,-41,18,0]
need(all(heights[j-1]-(heights[j] if j<20 else 0) == positive.get(j,0)-negative.get(j,0) for j in range(1,21)), 'Jump identity')
need(min(Q(h,256) for h in heights) >= 1-Q(36,11), 'Dual lower constraint')
need(max(heights) <= 256, 'Dual upper constraint')
need(Q(sum(heights),512) == Q(625,512), 'Zero kernel')
moment = sum(Q(abs(h),256)*Q(2,3)*Q((j+1)**3-j**3,64) for j,h in enumerate(heights))
need(moment == Q(134917,8192), 'Absolute second moment')
need(Q(611,500)+Q(674585,134217728) < Q(123,100), 'Continuum margin')
need(Q(100,123) > Q(4,5), 'Obstruction margin')

def bound(k):
    if k == 0:
        return 1220704
    p,n = 0,0
    for j in range(1,21):
        r = checked(j*k)%512
        flipped = r>256
        if flipped:
            r = checked(512-r)
        if r>128:
            r = checked(256-r)
        need(r<=128, 'Folded C argument')
        s = sine(r)
        a,b = positive.get(j,0),negative.get(j,0)
        if flipped:
            a,b = b,a
        p = checked(p+checked(a*s))
        n = checked(n+checked(b*s))
    absolute = checked(abs(p-n))
    numerator = checked((checked(absolute+255)//256)*256000000)
    denominator = checked(checked(2*3141592653)*k)
    return checked(checked(checked(numerator+denominator)-1)//denominator+200)

maximum_error = Q(0)
for r in range(129):
    z = Q(3141592654*r//256,10**9)
    polynomial = sum((-1)**n*z**(2*n+1)/math.factorial(2*n+1) for n in range(9))
    error = abs(Q(sine(r),10**9)-polynomial)
    maximum_error = max(maximum_error,error)
    need(error <= Q(1,50000000), 'Rational sine/polynomial cell '+str(r))
for m in range(512):
    r=m
    sign=-1 if r>256 else 1
    if r>256:r=512-r
    if r>128:r=256-r
    need(abs(math.sin(math.pi*m/256)-sign*math.sin(math.pi*r/256)) < 3e-15, 'Fold convention diagnostic')
libpath=HERE/'dual_grid_diagnostic.so'
command=['cc','-std=c11','-O2','-Wall','-Wextra','-Werror','-shared','-fPIC','-Dmain=diagnostic_unused_main',str(SOURCE),'-o',str(libpath)]
subprocess.run(command,check=True,capture_output=True)
lib=ctypes.CDLL(str(libpath))
lib.sine_fixed.argtypes=[ctypes.c_uint64]
lib.sine_fixed.restype=ctypes.c_uint64
lib.sample_bound.argtypes=[ctypes.c_uint64]
lib.sample_bound.restype=ctypes.c_uint64
lib.rh_dual_bound.restype=ctypes.c_uint64
need(all(lib.sine_fixed(r)==sine(r) for r in range(129)), 'Actual C sine comparison')
values=[bound(k) for k in range(257)]
need(all(lib.sample_bound(k)==values[k] for k in range(257)), 'Actual C grid comparison')
need(max(values)==1221161==lib.rh_dual_bound(), 'Actual C maximum')
result=dict(status='PASS_FINITE_DIAGNOSTICS_NOT_PV', sine_cells=129, grid_cells=257, fold_period_cells=512, source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(), compile_command=command, maximum_rational_rounding_error_float=float(maximum_error), maximum_u64_intermediate=largest, u64_limit=LIMIT, moment=str(moment), obstruction_floor='100/123', source_first_PV=False)
(HERE/'finite_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
