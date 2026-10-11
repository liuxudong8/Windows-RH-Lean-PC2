# diag9_5077.py : the epsilon-vs-rank discriminator — 37a1 (eps=-1, rank 1)
# 37a1: y^2+y = x^3-x, N=37, eps=-1, rank 1, true L'(1) = 0.305999773834052 (Sage lfunctions).
# Same upper-incomplete pipeline.  If slope ~ +0.306 -> pipeline fine for eps=-1 (rank 1),
# then 5077's -0.1477 is rank-driven (rank 3) deterioration.  If slope wrong -> eps=-1 driven.
import math
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from probe389_numeric import gen_a_n, gamma_upper

N37 = 37
EPS37 = -1.0
SQN37 = math.sqrt(N37)

def F37(s, Q):
    gs = math.gamma(s); g2s = math.gamma(2.0 - s)
    S1 = 0.0; S2 = 0.0
    for n in range(1, Q + 1):
        bn = 2.0 * math.pi * n / SQN37
        S1 += an37[n] * n ** (-s) * gamma_upper(s, bn) / gs
        S2 += an37[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn) / g2s
    C = N37 ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
    return S1 + C * S2 / EPS37

an37 = gen_a_n(2000, 0, 0, 1, -1, 0, {37: 1})  # 37a1, bad prime a_37 = +1 (split mult)

print("37a1 (eps=-1, rank 1) upper-incomplete pipeline:")
for Q in (300, 600, 1000, 2000):
    f0 = F37(1.0, Q)
    sl = (F37(1.0 + 0.01, Q) - F37(1.0 - 0.01, Q)) / 0.02
    print(f"Q={Q:5d}  F(1) = {f0:+.3e}   slope = {sl:+.9f}   (true L'(1) = +0.3059997738)")
