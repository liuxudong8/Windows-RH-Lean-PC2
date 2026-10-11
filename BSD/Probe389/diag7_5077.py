# diag7_5077.py : float vs mpmath, both curves, several Q — find where slope diverges
import math
import mpmath as mpm
mpm.mp.dps = 60

from probe5077_numeric import N, EPS, gen_a_n, gamma_upper, F_L
from probe389_numeric import gen_a_n as gen389

def slope_float(NN, ee, aaq, Q, h=0.01):
    F = lambda s: F_L(s, aaq, Q) if NN == 5077 else _F389(s, aaq, Q)
    return (F(1.0 + h) - F(1.0 - h)) / (2.0 * h)

def _F389(s, aaq, Q):
    N389 = 389
    gs = math.gamma(s); g2s = math.gamma(2.0 - s)
    S1 = 0.0; S2 = 0.0
    sq = math.sqrt(N389)
    for n in range(1, Q + 1):
        bn = 2.0 * math.pi * n / sq
        S1 += aaq[n] * n ** (-s) * gamma_upper(s, bn) / gs
        S2 += aaq[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn) / g2s
    C = N389 ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
    return S1 + C * S2 / 1.0

def slope_mp(NN, ee, aaq, Q, h=mpm.mpf('0.01')):
    sq = mpm.sqrt(NN)
    def F(s):
        gs = mpm.gamma(s); g2s = mpm.gamma(2 - s)
        S1 = mpm.mpf('0'); S2 = mpm.mpf('0')
        for n in range(1, Q + 1):
            bn = 2 * mpm.pi * n / sq
            nm = mpm.mpf(n)
            S1 += aaq[n] * nm ** (-s) * mpm.gammainc(s, 0, bn) / gs
            S2 += aaq[n] * nm ** (s - 2) * mpm.gammainc(2 - s, 0, bn) / g2s
        C = NN ** (1 - s) * (2 * mpm.pi) ** (2 * s - 2) / gs
        return S1 + C * S2 / ee
    return (F(1 + h) - F(1 - h)) / (2 * h)

an5077 = gen_a_n(20000)
an389 = gen389(3000, 0, 1, 1, -2, 0, {389: 1})

print("slope [F(1.01)-F(0.99)]/0.02 :")
print("curve   Q     float            mpmath(dps60)")
for tag, NN, ee, aaq, Q in (
    ("5077", N, EPS, an5077, 1000),
    ("5077", N, EPS, an5077, 2000),
    ("5077", N, EPS, an5077, 5000),
    ("5077", N, EPS, an5077, 10000),
    ("389 ", 389, 1.0, an389, 1000),
    ("389 ", 389, 1.0, an389, 3000),
):
    sf = slope_float(NN, ee, aaq, Q)
    sm = slope_mp(NN, ee, aaq, Q)
    print(f"{tag} {Q:6d} {sf:+.9f}   {mpm.nstr(sm, 12)}")
