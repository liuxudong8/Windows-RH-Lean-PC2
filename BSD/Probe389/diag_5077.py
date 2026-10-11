# diag_5077.py : Taylor structure of F(s) near s=1 for 5077a1
# If the pipeline is right: F(1+h) ~ L'''(1)/6 * h^3  (rank 3 fingerprint),
# i.e. log|F(1+h)| ~ 3 log h + const, no h^2 or h^1 contamination.
import math
from probe5077_numeric import N, EPS, gen_a_n, gamma_upper, SQN

Q = 10000
an = gen_a_n(Q)

def F_L(s):
    gs = math.gamma(s)
    g2s = math.gamma(2.0 - s)
    S1 = 0.0
    S2 = 0.0
    for n in range(1, Q + 1):
        bn = 2.0 * math.pi * n / SQN
        S1 += an[n] * n ** (-s) * gamma_upper(s, bn) / gs
        S2 += an[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn) / g2s
    C = N ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
    return S1 + C * S2 / EPS

print("s         F(s)             log10|F-0| slope-per-decade")
prev = None
for h in (0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002, 0.001):
    f = F_L(1.0 + h)
    s = math.copysign(1.0, f)
    L = math.log10(abs(f)) if abs(f) > 0 else -99
    slope = (L - prev) / math.log10(0.5) if prev is not None else float('nan')
    print(f"1+{h:5.3f}  {f:+.12e}  log10={L:8.3f}  slope={slope:6.2f}")
    prev = L
print("h=0      F(1) =", F_L(1.0))
print()
print("expect: F(1+h) ~ +1.7318*h^3 ;  slope ~ 3.0 (pure cubic)")
