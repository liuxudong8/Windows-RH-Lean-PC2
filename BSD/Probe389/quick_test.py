# quick_test.py — validate F_L formula against direct Dirichlet series in the
# absolute convergence strip (Re s > 3/2). If ratio != 1, the formula is wrong.
import sys
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P
import math

an389 = P.gen_a_n(3000, 0, 1, 1, -2, 0, bad_ap={389: 1})
an37 = P.gen_a_n(3000, 0, 0, 1, -1, 0, bad_ap={37: -1})

def S1(s, an, N, Q):
    sqN = math.sqrt(N)
    g = math.gamma(s)
    return sum(an[n] * n ** (-s) * P.gamma_upper(s, 2*math.pi*n/sqN) / g for n in range(1, Q+1))

for name, an, N, eps in (('389a1', an389, 389, 1), ('37a1', an37, 37, -1)):
    print(f'--- {name} ---')
    for s in (2.5, 3.0, 4.0):
        direct = sum(an[n] * n ** (-s) for n in range(1, 3001))
        fA = P.F_L(s, an, N, eps, 3000)
        fS1 = S1(s, an, N, 3000)
        print(f'  s={s}  direct={direct: .5f}  F={fA: .5f}  F/direct={fA/direct: .4f}  S1only/direct={fS1/direct: .4f}')
