# diag1.py — segment contributions of f(i/N) to locate wrong coefficients
import sys, math
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P

an389 = P.gen_a_n(6000, 0, 1, 1, -2, 0, bad_ap={389: 1})
N = 389
segs = [(1, 20), (21, 100), (101, 500), (501, 2000), (2001, 6000)]
for lo, hi in segs:
    s = 0.0
    for n in range(lo, hi + 1):
        s += an389[n] * math.exp(-2 * math.pi * n / N)
    print(f'n in [{lo},{hi}]: contribution = {s:+.4f}')
total = sum(an389[n] * math.exp(-2 * math.pi * n / N) for n in range(1, 6001))
print('total f(i/N) =', f'{total:.4f}', ' expect +-389*f(i) = +-0.7251')
fi = sum(an389[n] * math.exp(-2 * math.pi * n) for n in range(1, 20))
print('f(i) =', fi, ' 389*f(i) =', 389 * fi)
# also print raw coefficients in 21..60 for eyeballing
print('a_n n=21..60:', [an389[n] for n in range(21, 61)])
