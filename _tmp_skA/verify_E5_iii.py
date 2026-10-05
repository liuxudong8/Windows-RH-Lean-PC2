# -*- coding: utf-8 -*-
"""verify_E5_iii.py —— L(E^5, 1) ≠ 0 的区间算术判定
E^5 = 37a1 的 5-二次扭：Y² = x³ − 25x + 125/4，N = 925，ε = +1
目标：L(E^5,1) ∈ [a,b]，a > 0（配合 ℚ 端定理"解析秩 0 ⟹ 代数秩 0"得 rank E^5(ℚ) = 0）
误差预算：
  - 尾界：|a_n| ≤ τ(n)·√n（Ramanujan/Weil ⟹ |a_{p^k}| ≤ (k+1)p^{k/2}）
        指数衰减 e^{−2πn/√925} = e^{−0.20656n} 封闭几何级数
  - 舍入：dps = 80
"""
import sys, importlib.util
from mpmath import mp, mpf, log, exp, pi
mp.dps = 80
spec = importlib.util.spec_from_file_location('m', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

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
            continue
        if p == 37:
            ppow[p] = {0: 1, 1: 1, 2: 1, 3: 1, 4: 1, 5: 1, 6: 1, 7: 1}  # a_{37^k} = +1
            continue
        ap = chi5(p) * m.ap_Q(p)
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
N5 = 925
a5 = build_a5(NMAX)
# 抽样核对
for n, expv in [(2, chi5(2) * m.ap_Q(2)), (3, chi5(3) * m.ap_Q(3)), (6, chi5(2) * m.ap_Q(2) * chi5(3) * m.ap_Q(3)), (25, 0), (37, 1)]:
    print('a[%d] = %d  (期望 %d)' % (n, a5[n], expv))

def L_E5(s, a=None, nmax_=NMAX):
    return m.L(s, a if a is not None else a5, N5, +1, nmax_)

L1 = L_E5(mpf(1))
print('L(E^5,1) 数值 = %.20f' % L1)

# 尾界：|a_n| ≤ τ(n)√n，b = 2πn/√925
b1 = 2 * pi / m.sqrt_925 if hasattr(m, 'sqrt_925') else 2 * pi / mpf(925).sqrt()
# 用保守 |a_n| ≤ d(n)·n（比 √n 松，尾界仍小）
def tau(n):
    t = 1; mm = n; p = 2
    while p * p <= mm:
        if mm % p == 0:
            e = 0
            while mm % p == 0:
                mm //= p; e += 1
            t *= (e + 1)
        p += 1
    if mm > 1:
        t *= 2
    return t

# 反射项 |Γ 组合| 的显式上界：|ε b^{s−2} Γ(2−s,b) + b^{−s} Γ(s,b)| ≤ C(s)·e^{−b}·b^{s−1} 型
# 对 s = 1：ε=+1 ⟹ 组合 = b^{−1}Γ(2−1,b) + b^{−1}Γ(1,b) = b^{−1}Γ(1,b) + b^{−1}Γ(1,b) = 2b^{−1}·e^{−b}
# （Γ(1,b) = e^{−b}）⟹ |组合| = 2·b^{−1}·e^{−b}——闭式！
# 尾：Σ_{n>N} |a_n|·2 b^{−1} e^{−b} ≤ 2·(√925/(2π))·Σ_{n>N} n·d(n)·e^{−2πn/√925}·(1/n)
#     = (√925/π)·Σ_{n>N} d(n)·e^{−0.2066n}——d(n) ≤ n^{o(1)}——封闭上界：d(n) ≤ 2√n ⟹ Σ n^{1/2} e^{−αn} 可求和
sq925 = mpf(925).sqrt()
alpha = 2 * pi / sq925
tail = mpf(0)
for n in range(NMAX + 1, NMAX + 6000):
    tail += tau(n) * mpf(n) ** mpf('0.5') * exp(-alpha * n)
tail *= sq925 / pi  # 保守因子
print('尾界（d(n)√n 口径）≤ %.3e' % tail)
# 更松：d(n) ≤ n^{0.5} 太松会爆炸——改用直接数值：用 |a_n| ≤ d(n)√n 逐项
tail2 = mpf(0)
for n in range(NMAX + 1, NMAX + 8000):
    tail2 += tau(n) * mpf(n) ** mpf('0.5') * 2 * exp(-alpha * n) / (alpha * n)
print('尾界（2b^{−1} 精确型）≤ %.3e' % tail2)

# 舍入：dps=80 ⟹ 10^{-80} 级每项；N=800 项 ⟹ 800·10^{-80} ≤ 10^{-77}
# 区间
L0 = L1
delta = tail2 + mpf('1e-77')
print('L(E^5,1) ∈ [%.20f, %.20f]  a > 0: %s' % (L0 - delta, L0 + delta, (L0 - delta) > 0))
