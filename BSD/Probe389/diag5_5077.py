# diag5_5077.py : (a) Q-scaling of the spurious first-order term  (b) cubic extraction of L'''/6
# rank-3: L'(1)=0, L''(1)=0, L'''(1)/6 = 1.73184990 (Cremona).
# Spurious slope ~ O(Q^{-1/2})  => doubling Q cuts slope by sqrt(2).
# 4th-order central difference D = [F(1+2h)-2F(1+h)+2F(1-h)-F(1-2h)]/(2h^3) kills f',f'' and gives F''' = L'''.
import math
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from probe5077_numeric import N, EPS, gen_a_n, gamma_upper

SQN = math.sqrt(N)

def make_F(Q):
    an = gen_a_n(Q)
    def F(s):
        gs = math.gamma(s)
        g2s = math.gamma(2.0 - s)
        S1 = 0.0; S2 = 0.0
        for n in range(1, Q + 1):
            bn = 2.0 * math.pi * n / SQN
            S1 += an[n] * n ** (-s) * gamma_upper(s, bn) / gs
            S2 += an[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn) / g2s
        C = N ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
        return S1 + C * S2 / EPS
    return F

print("== (a) spurious slope [F(1+h)-F(1-h)]/2h  vs  Q ==")
prev = None
for Q in (5000, 10000, 20000, 40000):
    F = make_F(Q)
    h = 0.01
    s1 = (F(1.0 + h) - F(1.0 - h)) / (2 * h)
    s2 = (F(1.0 + 2 * h) - F(1.0 - 2 * h)) / (4 * h)
    print(f"Q={Q:6d}  slope(2h={h}) = {s1:+.6f}   slope(4h={2*h}) = {s2:+.6f}")
    if prev is not None:
        print(f"           ratio vs Q/2 = {s1/prev:+.4f}   (expect ~1/sqrt(2) = 0.707 if truncation-driven)")
    prev = s1
print()

print("== (b) cubic extraction L'''/6  (4th-order central diff, kills linear term) ==")
for Q in (10000, 40000):
    F = make_F(Q)
    print(f"Q={Q}:")
    for h in (0.20, 0.10, 0.05, 0.02, 0.01):
        D = (F(1.0 + 2*h) - 2*F(1.0 + h) + 2*F(1.0 - h) - F(1.0 - 2*h)) / (2 * h**3)
        print(f"   h={h:5.2f}  L'''/6 = {D/6:+.6f}   (Cremona 1.73184990)")
