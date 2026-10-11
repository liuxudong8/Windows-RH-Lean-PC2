# diag3_5077.py : control — Taylor scaling of F(1+h) for 389a1 (rank 2, eps=+1)
# If pipeline is healthy: slope ~ 2 (quadratic, L'(1)=0 forced by rank 2).
import math
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from probe389_numeric import gen_a_n, gamma_upper, F_L

N389 = 389
an = gen_a_n(3000, 0, 1, 1, -2, 0, {389: 1})  # 389a1
SQN = math.sqrt(N389)
Q = 3000

def F389(s):
    gs = math.gamma(s)
    g2s = math.gamma(2.0 - s)
    S1 = 0.0; S2 = 0.0
    for n in range(1, Q + 1):
        bn = 2.0 * math.pi * n / SQN
        S1 += an[n] * n ** (-s) * gamma_upper(s, bn) / gs
        S2 += an[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn) / g2s
    C = N389 ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
    return S1 + C * S2 / 1.0   # eps_L = +1 for 389a1

prev = None
out = []
for h in (0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002, 0.001):
    f = F389(1.0 + h)
    L = math.log10(abs(f)) if abs(f) > 0 else -99
    slope = (L - prev) / math.log10(0.5) if prev is not None else float('nan')
    out.append(f"1+{h:5.3f}  {f:+.12e}  log10={L:8.3f}  slope={slope:6.2f}")
    prev = L
print("389a1 (rank 2, eps=+1) control:")
print("\n".join(out))
print(f"F(1) = {F389(1.0):.3e}   (rank 2: L(1) should be 0;  expect slope ~ 2.0)")
