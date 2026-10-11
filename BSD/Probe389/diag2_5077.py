# diag2_5077.py : split F(1+h) = S1 + C*S2'/eps ; locate the linear pollution
import math
from probe5077_numeric import N, EPS, gen_a_n, gamma_upper, SQN

Q = 10000
an = gen_a_n(Q)

def split_F(s):
    gs = math.gamma(s)
    g2s = math.gamma(2.0 - s)
    S1 = 0.0
    S2 = 0.0
    for n in range(1, Q + 1):
        bn = 2.0 * math.pi * n / SQN
        S1 += an[n] * n ** (-s) * gamma_upper(s, bn) / gs
        S2 += an[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn) / g2s
    C = N ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
    return S1, C * S2 / EPS

print("h      S1(1+h)          C*S2'/eps(1+h)     F=sum         dS1/h      dFE/h")
prev_S1 = None; prev_FE = None
for h in (0.2, 0.1, 0.05, 0.02, 0.01):
    s = 1.0 + h
    S1, FE = split_F(s)
    Fv = S1 + FE
    dS1 = (S1 - prev_S1) / (h - prev_h) if prev_S1 is not None else float('nan')
    dFE = (FE - prev_FE) / (h - prev_h) if prev_FE is not None else float('nan')
    print(f"{h:5.2f} {S1:+.10e} {FE:+.10e} {Fv:+.10e}   {dS1:+.4f} {dFE:+.4f}")
    prev_S1, prev_FE, prev_h = S1, FE, h
print("F(1) split: ", split_F(1.0))
print("expect: S1 ~ const, FE ~ -const at s=1 (exact cancel -> F(1)=0);")
print("near 1: linear parts dS1/h and dFE/h must cancel to O(h^2) for rank 3.")
