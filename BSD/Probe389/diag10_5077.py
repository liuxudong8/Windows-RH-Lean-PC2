# diag10_5077.py : post-fix verification — h->0 extrapolation of L'''/6 and Lambda symmetry
import math
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from probe5077_numeric import N, EPS, gen_a_n, F_L, d3

Q = 10000
an = gen_a_n(Q)
F = lambda s: F_L(s, an, Q)

print("== post-fix L'''/6 h-scan (target 1.73184990) ==")
rows = []
for h in (0.4, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002):
    v = d3(F, 1.0, h) / 6.0
    rows.append((h, v))
    print(f"h={h:5.3f}  L'''/6 = {v:.6f}   dev={100*(v/1.73184990-1):+.4f}%")
# Richardson-ish extrapolation on h^2 for last 3 points
h1, v1 = rows[-2]
h2, v2 = rows[-1]
ext = v2 + (v2 - v1) / (h1**2 / h2**2 - 1) if h1 != h2 else float('nan')
print(f"h^2-linear extrapolation from h={h1:.3f},{h2:.3f}: L'''/6 ~ {ext:.6f}  (target 1.73184990)")
print()
print("== post-fix Lambda(1+h)/Lambda(1-h)  (expect -1 + O(h^2); pre-fix deviated ~O(h)) ==")
def Lam(s):
    return N ** (s / 2.0) * (2.0 * math.pi) ** (-s) * math.gamma(s) * F_L(s, an, Q)
prev_dev = None
for h in (0.05, 0.02, 0.01, 0.005, 0.002):
    r = Lam(1 + h) / Lam(1 - h)
    dev = r + 1.0
    print(f"h={h:5.3f}  ratio = {r:+.9f}  dev from -1 = {dev:+.3e}")
    if prev_dev is not None:
        print(f"          dev ratio vs previous h = {dev/prev_dev:+.3f}  (4 if O(h^2), 2 if O(h))")
    prev_dev = dev
