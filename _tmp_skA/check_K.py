# -*- coding: utf-8 -*-
"""K 端（ℚ(√5)）核对：s=3 一致性 + 高精度 L_K'(1)"""
import sys, importlib.util
from mpmath import mp, mpf, gammainc, gamma, pi
mp.dps = 60
spec = importlib.util.spec_from_file_location('skA_ext', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

NK = 1369
nmax = 800
bK = m.build_bK(800) if hasattr(m, 'build_bK') else None
# 重新构造 bK（用 m 模块内函数）
nmaxK = 800
bK = [0] * (nmaxK + 1)
bK[1] = 1
split_tab, inert_tab, ram_tab = {}, {}, {}
for p in range(2, nmaxK + 1):
    isp = True
    d = 2
    while d * d <= p:
        if p % d == 0:
            isp = False
            break
        d += 1
    if not isp:
        continue
    if m.is_split(p):
        K = 0; pkv = p
        while pkv <= nmaxK:
            K += 1; pkv *= p
        split_tab[p] = m.local_split_coeffs(m.ap_Q(p), p, K)
    elif p == 5:
        K = 0; pkv = 5
        while pkv <= nmaxK:
            K += 1; pkv *= 5
        ram_tab = m.local_inert_coeffs(m.ap_Q(5), 5, K)
    else:
        K = 0; pkv = p * p
        while pkv <= nmaxK:
            K += 1; pkv *= p * p
        if p == 37:
            inert_tab[37] = [1] * (K + 1)
        else:
            a = m.ap_Q(p) ** 2 - 2 * p
            inert_tab[p] = m.local_inert_coeffs(a, p, K)
for n in range(2, nmaxK + 1):
    mm = n; val = 1; p = 2
    while p * p <= mm:
        if mm % p == 0:
            e = 0
            while mm % p == 0:
                mm //= p; e += 1
            if p == 5:
                val *= ram_tab[e]
            elif m.is_split(p):
                val *= split_tab[p][e]
            else:
                if e % 2 == 1:
                    val = 0
                else:
                    val *= inert_tab[p][e // 2]
        p += 1
    if mm > 1:
        if mm == 5:
            val *= ram_tab[1]
        elif m.is_split(mm):
            val *= split_tab[mm][1]
        else:
            val = 0
    bK[n] = val

# s=3 一致性
s3 = mpf(3)
direct = mpf(0)
for n in range(1, nmax + 1):
    direct += bK[n] * (mpf(n) ** (-s3))
lam3 = m.Lambda(s3, bK, NK, -1, nmax)
formula = (2 * pi / mpf(NK) ** 0.5) ** s3 / gamma(s3) * lam3
print('L_K_dir(3) =', direct)
print('L_K_fml(3) =', formula)
print('ratio       =', formula / direct)

# Richardson 外推 L_K'(1)
def L(s):
    return m.L(s, bK, NK, -1, nmax)
h1, h2 = mpf('1e-2'), mpf('1e-3')
d1 = (L(1 + h1) - L(1 - h1)) / (2 * h1)
d2 = (L(1 + h2) - L(1 - h2)) / (2 * h2)
rich = d2 + (d2 - d1) / 3   # O(h²) 外推
print("L_K'(1) h=1e-2:", d1)
print("L_K'(1) h=1e-3:", d2)
print("L_K'(1) Richardson:", rich)

# ℚ 端同样 Richardson
coeffsQ = m.build_bn(800, m.ap_Q, {37}, 'ell')
def Lq(s):
    return m.L(s, coeffsQ, 37, -1, 800)
dq1 = (Lq(1 + h1) - Lq(1 - h1)) / (2 * h1)
dq2 = (Lq(1 + h2) - Lq(1 - h2)) / (2 * h2)
print("ℚ L'(1) Richardson:", dq2 + (dq2 - dq1) / 3, '（LMFDB 0.3059997738346523）')
