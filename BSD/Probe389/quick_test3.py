# quick_test3.py — confirm epsN = +1 for both curves at s = 2.5 (in-band only)
import sys, math
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P

an389 = P.gen_a_n(3000, 0, 1, 1, -2, 0, bad_ap={389: 1})
an37 = P.gen_a_n(3000, 0, 0, 1, -1, 0, bad_ap={37: -1})

def parts(s, an, N, Q):
    sqN = math.sqrt(N)
    g1 = math.gamma(s)
    S1 = S2p = 0.0
    for n in range(1, Q + 1):
        b = 2 * math.pi * n / sqN
        S1 += an[n] * n ** (-s) * P.gamma_upper(s, b) / g1
        S2p += an[n] * n ** (s - 2) * P.gamma_upper(2 - s, b)
    return S1, S2p

for name, an, N in (('389a1', an389, 389), ('37a1', an37, 37)):
    s = 2.5
    direct = sum(an[n] * n ** (-s) for n in range(1, 3001))
    S1, S2p = parts(s, an, N, 3000)
    C = N ** (1 - s) * (2 * math.pi) ** (2 * s - 2) / math.gamma(s)
    print(f'{name}: s={s}  direct={direct:.6f}  S1={S1:.6f}  S2p={S2p:.6f}  C={C:.6f}')
    for en in (+1, -1):
        F = S1 + C / en * S2p
        print(f'   epsN={en:+d}: F={F: .6f}  |F-direct|={abs(F-direct):.5f}')
