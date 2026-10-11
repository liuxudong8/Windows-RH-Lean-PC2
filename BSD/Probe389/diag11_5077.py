# diag11_5077.py : post-fix F'', F' h-scans (rank 3: both -> 0) + clean L'''/6 window
import math
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from probe5077_numeric import N, EPS, gen_a_n, F_L

Q = 10000
an = gen_a_n(Q)
F = lambda s: F_L(s, an, Q)

print("== post-fix h-scans at s=1 (rank 3: F' -> 0, F'' -> 0, F'''/6 -> 1.73184990) ==")
for h in (0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002):
    d1 = (F(1 + h) - F(1 - h)) / (2 * h)
    d2 = (F(1 + h) - 2 * F(1) + F(1 - h)) / (h * h)
    d3 = (F(1 + 2*h) - 2*F(1 + h) + 2*F(1 - h) - F(1 - 2*h)) / (2 * h**3)
    print(f"h={h:5.3f}  F'  = {d1:+.6f}   F'' = {d2:+.6f}   F'''/6 = {d3/6:+.6f}")
