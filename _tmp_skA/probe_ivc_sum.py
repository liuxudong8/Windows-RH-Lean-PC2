# -*- coding: utf-8 -*-
"""probe_ivc_sum.py —— 正负项分离的粗界下界数值
S_N = Σ_{n<=N} a_n n^{-1} e^{-αn}（α = 2π/√925 ≈ 0.206489）
正项下界：Σ_+ a_n n^{-1} q-^n（q- = 0.8133）；负项上界：Σ_- |a_n| n^{-1} q+^n（q+ = 0.8136）
LB(N) = P- - M+ 必须 > 2.675（给尾界留余量）
"""
import sys
from mpmath import mp, mpf, exp, pi
mp.dps = 80

def legendre_sq_count(p, f):
    n = 0
    for x in range(p):
        r = f(x) % p
        if r == 0:
            n += 1
        elif pow(r, (p - 1) // 2, p) == 1:
            n += 2
    return n

def count_Fp_y2y(p):
    return legendre_sq_count(p, lambda x: 4 * x * x * x - 4 * x + 1)

def ap_Q(p):
    if p == 37:
        return -1
    return p - count_Fp_y2y(p)

def chi5(p):
    r = p % 5
    return 1 if r in (1, 4) else -1

def build_a5(nmax):
    a = [0] * (nmax + 1)
    a[1] = 1
    ppow = {}
    for p in range(2, nmax + 1):
        isp = True; d = 2
        while d * d <= p:
            if p % d == 0:
                isp = False; break
            d += 1
        if not isp:
            continue
        if p == 5:
            ppow[p] = {0: 1}
            continue
        if p == 37:
            ppow[p] = {k: 1 for k in range(0, 8)}
            continue
        ap = chi5(p) * ap_Q(p)
        ppow[p] = {0: 1, 1: ap}
        pk = p * p; k = 2
        while pk <= nmax:
            ppow[p][k] = ap * ppow[p][k - 1] - p * ppow[p][k - 2]
            pk *= p; k += 1
    for n in range(2, nmax + 1):
        mm = n; val = 1; p = 2
        while p * p <= mm:
            if mm % p == 0:
                e = 0
                while mm % p == 0:
                    mm //= p; e += 1
                if p == 5:
                    val *= 0
                elif p == 37:
                    val *= 1
                else:
                    val *= ppow[p][e]
            p += 1
        if mm > 1:
            if mm == 5:
                val *= 0
            elif mm == 37:
                val *= 1
            else:
                val *= ppow[mm][1]
        a[n] = val
    return a

NMAX = 800
a5 = build_a5(NMAX)
qminus = mpf('0.8133')
qplus = mpf('0.8136')

for N in [50, 100, 200]:
    P = mpf('0'); M = mpf('0')
    for n in range(1, N + 1):
        an = a5[n]
        if an > 0:
            P += an * qminus ** n / n
        elif an < 0:
            M += (-an) * qplus ** n / n
    LB = P - M
    print('N=%d  P- = %.15f  M+ = %.15f  LB = %.15f  (2LB = %.12f, 目标 2.675)' % (N, P, M, LB, 2 * LB))

# 分块下界（每块 25 项）——为 Lean norm_num 分块做准备
N = 100
block = 25
for j in range(0, N, block):
    lo, hi = j + 1, min(j + block, N)
    P = mpf('0'); M = mpf('0')
    for n in range(lo, hi + 1):
        an = a5[n]
        if an > 0:
            P += an * qminus ** n / n
        elif an < 0:
            M += (-an) * qplus ** n / n
    print('块[%3d..%3d]  P=%.15f  M=%.15f  LB=%.15f' % (lo, hi, P, M, P - M))
