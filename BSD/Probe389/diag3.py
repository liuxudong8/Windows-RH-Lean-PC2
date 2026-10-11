# diag3.py — Fricke at t = 0.5, 1, 2: look for a systematic ratio pattern
import sys, math
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P

an389 = P.gen_a_n(6000, 0, 1, 1, -2, 0, bad_ap={389: 1})
an37 = P.gen_a_n(6000, 0, 0, 1, -1, 0, bad_ap={37: 1})
N = 389

for t in (0.5, 1.0, 2.0):
    f_it = sum(an389[n] * math.exp(-2 * math.pi * t * n) for n in range(1, 25))
    s = 0.0
    for n in range(1, 6001):
        e = math.exp(-2 * math.pi * n / (N * t))
        s += an389[n] * e
        if e < 1e-15:
            break
    # Fricke: f(i/(Nt)) = -epsN * N * t^2 * f(it);  two hypotheses epsN = +-1
    print(f'389a1 t={t}: actual f(i/(Nt)) = {s:+.6f}   (-N t^2 f(it)) = {-N*t*t*f_it:+.6f}   (+N t^2 f(it)) = {+N*t*t*f_it:+.6f}')
    print(f'         ratios: {s/(-N*t*t*f_it):.3f}  /  {s/(N*t*t*f_it):.3f}')

N37 = 37
for t in (1.0, 2.0):
    f_it = sum(an37[n] * math.exp(-2 * math.pi * t * n) for n in range(1, 25))
    s = 0.0
    for n in range(1, 6001):
        e = math.exp(-2 * math.pi * n / (N37 * t))
        s += an37[n] * e
        if e < 1e-15:
            break
    print(f'37a1  t={t}: actual = {s:+.6f}   (+-N t^2 f(it)) = {N37*t*t*f_it:+.6f}')
    print(f'         ratios: {s/(-N37*t*t*f_it):.3f}  /  {s/(N37*t*t*f_it):.3f}')
