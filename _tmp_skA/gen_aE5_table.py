# -*- coding: utf-8 -*-
"""gen_aE5_table.py —— 生成 a_n(E^5) 前 800 项为 Lean 值表
E^5 = 37a1 的 5-二次扭：a_p = chi5(p)*a_p(E)（p∤925），a_5 = 0，a_37 = +1
素幂递推 a_{p^{k+1}} = a_p a_{p^k} - p a_{p^{k-1}}（好素）；乘性组装
同时输出部分和数值核验（mpmath 80 位）
"""
import math
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
# 抽样核对
for n in [1, 2, 3, 4, 5, 6, 10, 11, 25, 37, 49, 100]:
    print('a[%d] = %d' % (n, a5[n]))

# 部分和数值核验：S = Σ_{n<=N} a_n n^{-1} e^{-2πn/√925}
sq925 = mpf(925).sqrt()
alpha = 2 * pi / sq925
for N in [50, 100, 200, 800]:
    S = mpf('0')
    for n in range(1, N + 1):
        S += a5[n] * exp(-alpha * n) / n
    print('S_%d = %.25f  (2S = %.20f)' % (N, S, 2 * S))

# 写 Lean 值表
with open(r'c:\proj2\BSD\aE5_table.lean', 'w', encoding='utf-8') as f:
    f.write('-- 自动生成：a_n(E^5) 前 %d 项（N=925, eps=+1；a_5=0, a_37=+1）\n' % NMAX)
    f.write('noncomputable def aE5 : Nat -> Int\n')
    f.write('| 0 => 0\n')
    for n in range(1, NMAX + 1):
        f.write('| %d => %d\n' % (n, a5[n]))
    f.write('| _ => 0\n')
print('表已写入 c:\\proj2\\BSD\\aE5_table.lean，共 %d 行' % NMAX)
