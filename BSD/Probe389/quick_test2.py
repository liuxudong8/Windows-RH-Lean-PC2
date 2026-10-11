# quick_test2.py — decide the exact second-term factor of the convergent L-series formula
# Candidates (epsilon_N = Atkin-Lehner eigenvalue, +1 or -1):
#   L(s) = S1(s) + (1/epsN)*N^{1-s}(2pi)^{2s-2}/Gamma(s) * S2'(s)
#   S1 = sum a_n n^{-s} Gamma(s,b)/Gamma(s);  S2' = sum a_n n^{s-2} Gamma(2-s,b)
import sys, math
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P

an389 = P.gen_a_n(3000, 0, 1, 1, -2, 0, bad_ap={389: 1})
an37 = P.gen_a_n(3000, 0, 0, 1, -1, 0, bad_ap={37: -1})

def parts(s, an, N, Q):
    sqN = math.sqrt(N)
    g1 = math.gamma(s)
    g2 = math.gamma(2 - s)
    S1 = S2p = 0.0
    for n in range(1, Q + 1):
        b = 2 * math.pi * n / sqN
        S1 += an[n] * n ** (-s) * P.gamma_upper(s, b) / g1
        S2p += an[n] * n ** (s - 2) * P.gamma_upper(2 - s, b)
    return S1, S2p

for name, an, N, eps in (('389a1', an389, 389, 1), ('37a1', an37, 37, -1)):
    for s in (2.5, 3.0, 4.0):
        direct = sum(an[n] * n ** (-s) for n in range(1, 3001))
        S1, S2p = parts(s, an, N, 3000)
        C = N ** (1 - s) * (2 * math.pi) ** (2 * s - 2) / math.gamma(s)
        print(f'--- {name} s={s}  direct={direct:.5f}  S1={S1:.5f}  S2p={S2p:.5f}  C={C:.6f}')
        for en in (+1, -1):
            F = S1 + C / en * S2p
            print(f'    epsN={en:+d}:  F={F: .5f}   |F-direct|={abs(F-direct):.4f}')
