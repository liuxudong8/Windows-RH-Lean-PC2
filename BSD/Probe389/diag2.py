# diag2.py — Fricke at two points t=1 and t=2; if t=2 also fails with same ratio,
# the formula/epsN assumption is wrong; if t=1 fails alone, coefficients in some range are wrong.
import sys, math
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P

an389 = P.gen_a_n(6000, 0, 1, 1, -2, 0, bad_ap={389: 1})
N = 389
for t in (1, 2):
    f_it = sum(an389[n] * math.exp(-2 * math.pi * t * n) for n in range(1, 20))
    # f(i/(N t)) = sum a_n exp(-2 pi n / (N t)); converges (n~6000)
    s = 0.0
    for n in range(1, 6001):
        e = math.exp(-2 * math.pi * n / (N * t))
        s += an389[n] * e
        if e < 1e-15:
            break
    pred_plus = -N * (t * t) * f_it   # epsN = +1
    pred_minus = +N * (t * t) * f_it  # epsN = -1
    print(f't={t}: f(i/({N}t)) = {s:+.6f}   pred(epsN=+1) = {pred_plus:+.6f}   pred(epsN=-1) = {pred_minus:+.6f}')
    print(f'    ratios: actual/pred(+1) = {s/pred_plus:.3f}   actual/pred(-1) = {s/pred_minus:.3f}')
