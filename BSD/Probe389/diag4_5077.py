# diag4_5077.py : decisive — odd/even split of F(1+h) and functional-equation symmetry
# rank-3 fingerprint: F(1+h) odd part ~ L'''/6 h^3, even part ~ 0.
# Lambda(s) = N^{s/2} (2pi)^{-s} Gamma(s) F(s)  must satisfy Lambda(s) = eps * Lambda(2-s).
import math
from probe5077_numeric import N, EPS, gen_a_n, gamma_upper
from probe389_numeric import gen_a_n as gen389, gamma_upper as gu389
import sys

Q = 10000
an = gen_a_n(Q)
N389 = 389
an389 = gen389(3000, 0, 1, 1, -2, 0, {389: 1})  # 389a1, eps=+1

def F_L(s, NN, ee, aaq, q):
    gs = math.gamma(s)
    g2s = math.gamma(2.0 - s)
    S1 = 0.0
    S2 = 0.0
    sq = math.sqrt(NN)
    for n in range(1, q + 1):
        bn = 2.0 * math.pi * n / sq
        S1 += aaq[n] * n ** (-s) * gamma_upper(s, bn) / gs
        S2 += aaq[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn) / g2s
    C = NN ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
    return S1 + C * S2 / ee

def Lam(s, NN, ee, aaq, q):
    return NN ** (s / 2.0) * (2.0 * math.pi) ** (-s) * math.gamma(s) * F_L(s, NN, ee, aaq, q)

out = sys.stdout
print("== 5077 odd/even split of F(1+h) ==", file=out)
print("h       F(1+h)          F(1-h)           odd-part/h^3     even-part/h^2", file=out)
for h in (0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002):
    fp = F_L(1.0 + h, N, EPS, an, Q)
    fm = F_L(1.0 - h, N, EPS, an, Q)
    odd = (fp - fm) / 2.0
    evn = (fp + fm) / 2.0
    print(f"{h:5.2f} {fp:+.9e} {fm:+.9e} {odd/(h**3):+10.6f} {evn/(h*h):+10.6f}", file=out)
print("  expect odd/h^3 -> L'''/6 = 1.73185 ; even/h^2 -> L''/2 = 0", file=out)
print(file=out)
print("== Lambda symmetry: Lam(1+h)/Lam(1-h) ==", file=out)
print("curve   h=0.05      h=0.02      h=0.01      h=0.005      h=0.002   (5077 expect -1, 389 expect +1)", file=out)
for tag, NN, ee, aaq, q, expv in (("5077", N, EPS, an, Q, -1.0), ("389", N389, 1.0, an389, 3000, +1.0)):
    row = f"{tag}: "
    for h in (0.05, 0.02, 0.01, 0.005, 0.002):
        r = Lam(1.0 + h, NN, ee, aaq, q) / Lam(1.0 - h, NN, ee, aaq, q)
        row += f"{r:+.7f}  "
    print(row + f"  (expect {expv:+.0f})", file=out)
print(file=out)
print("== 5077 F(1+h) - F(1) vs h (slope) ==", file=out)
f0 = F_L(1.0, N, EPS, an, Q)
print(f"F(1) = {f0:+.9e}", file=out)
for h in (0.05, 0.02, 0.01, 0.005, 0.002):
    fp = F_L(1.0 + h, N, EPS, an, Q)
    fm = F_L(1.0 - h, N, EPS, an, Q)
    print(f"h={h:5.2f}  [F(1+h)-F(1-h)]/2h = {((fp-fm)/(2*h)):+.9f}   [F(1+h)+F(1-h)-2F(1)]/h^2 = {((fp+fm-2*f0)/(h*h)):+.9f}", file=out)

