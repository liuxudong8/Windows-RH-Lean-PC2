# -*- coding: utf-8 -*-
"""E^5（37a1 的 5-二次扭）：验证 L(E^5,1) ≠ 0 —— rank E^5(ℚ)=0 的解析端
二次扭分解：rank E(ℚ(√5)) = rank E(ℚ) + rank E^5(ℚ)
E^5: Y² = x³ − 25x + 125/4，N(E^5) = 37·25 = 925，a_p(E^5) = χ_5(p)·a_p(E)
根数：ε(E^5) = ε(E)·χ_5(−37) = −1·(−1) = +1 ⟹ 解析秩偶数（期望 0）
"""
import sys, importlib.util
from mpmath import mp, mpf, mpmathify, pi, log, gamma, gammainc
mp.dps = 60
spec = importlib.util.spec_from_file_location('m', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def chi5(p):
    # Legendre 符号 (p/5)
    r = p % 5
    return 1 if r in (1, 4) else -1

def ap5(p):
    a = m.ap_Q(p)
    return chi5(p) * a if p not in (5, 37) else (None if p == 37 else -1)

# 37a 在 5 处：好约化？—— 5 ∤ 37 ⟹ 5 是好素（对 E），a_5(E) = −2（skA 已验证）
# E^5 在 5 处：分歧（5 | d）——局部因子（1 − X)⁻¹（与 E 在 5 的 a 无关？）—— 二次扭在 d|p 处的系数：
# E^d 在 p|d 处：若 p 在 E 上好、在 E^d 上分歧——a_p(E^d) = ?—— 需要小心（通常用 Weierstrass 正规化）
# 简化处理：先构造 a_n(E^5) 对 n 不含 5 的因子，5 的贡献单独用 L 的欧拉积直接算（n = 5^k）

def build_a5(nmax):
    a = [0] * (nmax + 1)
    a[1] = 1
    # 素幂表：a[p^k]（p ∤ 925：Hecke 递推；37：乘性 ±1；5：加性 a=0）
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
            ppow[p] = {0: 1}  # a[5^k] = 0 for k>=1
            continue
        if p == 37:
            ppow[p] = {0: 1}  # 符号稍后统一设置
            continue
        ap = chi5(p) * m.ap_Q(p)
        ppow[p] = {0: 1, 1: ap}
        pk = p * p; k = 2
        while pk <= nmax:
            ppow[p][k] = ap * ppow[p][k - 1] - p * ppow[p][k - 2]
            pk *= p; k += 1
    # 乘性组合（标准因子分解）
    for n in range(2, nmax + 1):
        mm = n; val = 1; p = 2
        while p * p <= mm:
            if mm % p == 0:
                e = 0
                while mm % p == 0:
                    mm //= p; e += 1
                if p == 5:
                    val *= 0  # 加性：5 的系数全 0
                elif p == 37:
                    val *= 1  # 符号由 set_a37 统一覆盖
                else:
                    val *= ppow[p][e]
            p += 1
        if mm > 1:
            if mm == 5:
                val *= 0  # 加性：5 的系数全 0
            elif mm == 37:
                val *= 1  # 符号由 set_a37 统一覆盖
            else:
                val *= ppow[mm][1]
        a[n] = val
    return a

def set_a37(a, sign):
    # 37 乘性：a[37^k] = sign^k
    ppow = {0: 1}
    for k in range(1, 8):
        ppow[k] = sign ** k
    for n in range(2, nmax + 1):
        mm = n; e37 = 0
        while mm % 37 == 0:
            mm //= 37; e37 += 1
        if e37:
            rest = n // 37 ** e37
            a[n] = a[rest] * ppow[e37]
    return a

nmax = 600
a5 = build_a5(nmax)

def L_E5(s, N=925, w=+1, nmax_=nmax, a=None):
    return m.L(s, a if a is not None else a5, N, w, nmax_)

def L_dir5(s, a):
    tot = mpf(0)
    for n in range(1, nmax + 1):
        tot += a[n] * (mpf(n) ** (-s))
    return tot

# 37 处符号扫描：s=3 反射 vs 直接级数
for sgn in (1, -1):
    aa = a5[:]
    set_a37(aa, sgn)
    r = L_E5(mpmathify(3), a=aa) / L_dir5(mpmathify(3), aa)
    print('a_37=%+d: s=3 ratio=%.10f' % (sgn, r))

# 取正确符号重算 L(1)
sgn = -1 if (L_E5(mpmathify(3), a=set_a37(a5[:], -1)) / L_dir5(mpmathify(3), set_a37(a5[:], -1)) - 1) ** 2 < (L_E5(mpmathify(3), a=set_a37(a5[:], 1)) / L_dir5(mpmathify(3), set_a37(a5[:], 1)) - 1) ** 2 else 1
a5f = set_a37(a5[:], sgn)
print('选中 a_37 = %+d' % sgn)
L1 = L_E5(mpmathify(1), a=a5f)
print('L(E^5, 1) = %.15f   (|·|=%.3e)' % (L1, abs(L1)))
h = mpf('1e-3')
Lp1 = (L_E5(1 + h, a=a5f) - L_E5(1 - h, a=a5f)) / (2 * h)
print('L\'(E^5, 1) = %.12f' % Lp1)
