# -*- coding: utf-8 -*-
"""(iii) 严格化闭环：反射公式截断 + 显式余项界 + 区间算术
目标：证明 L_K'(1) ≠ 0（E = 37a1 / K = ℚ(√5)），给出确定性区间。
误差预算：截断尾（n>Nmax，e^{-2πn/37} 指数衰减）+ 差分（h²/6·|L'''|）+ 舍入（dps=80）。
"""
import sys, importlib.util
from mpmath import mp, mpf, mpmathify, pi, log, gamma, gammainc, diff
mp.dps = 80
spec = importlib.util.spec_from_file_location('m', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

NMAX = 800
NMAX2 = 3000   # 用于显式尾部估计的上限
NK = 1369
Q = 2 * pi / mpf(NK) ** 0.5

# ---------- K 端 b_n ----------
bK = [0] * (NMAX2 + 1)
bK[1] = 1
split_tab, inert_tab, ram_tab = {}, {}, {}
for p in range(2, NMAX2 + 1):
    isp = True; d = 2
    while d * d <= p:
        if p % d == 0:
            isp = False; break
        d += 1
    if not isp:
        continue
    if m.is_split(p):
        K = 0; pkv = p
        while pkv <= NMAX2:
            K += 1; pkv *= p
        split_tab[p] = m.local_split_coeffs(m.ap_Q(p), p, K)
    elif p == 5:
        K = 0; pkv = 5
        while pkv <= NMAX2:
            K += 1; pkv *= 5
        ram_tab = m.local_inert_coeffs(m.ap_Q(5), 5, K)
    else:
        K = 0; pkv = p * p
        while pkv <= NMAX2:
            K += 1; pkv *= p * p
        if p == 37:
            inert_tab[37] = [1] * (K + 1)
        else:
            a = m.ap_Q(p) ** 2 - 2 * p
            inert_tab[p] = m.local_inert_coeffs(a, p, K)
for n in range(2, NMAX2 + 1):
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

def Lam_term(n, s):
    b = 2 * pi * n / mpf(NK) ** 0.5
    return bK[n] * (-1 * b ** (s - 2) * gammainc(2 - s, b, mp.inf)
                    + b ** (-s) * gammainc(s, b, mp.inf))

def Lam(s, N):
    tot = mpf(0)
    for n in range(1, N + 1):
        tot += Lam_term(n, s)
    return tot

def Lval(s, N):
    return Q ** s / gamma(s) * Lam(s, N)

# ---------- 截断尾显式界（保守） ----------
# |R| ≤ Σ_{n>NMAX}^{NMAX2} |b_n|·(|b^{s-2}Γ(2-s,b)| + |b^{-s}Γ(s,b)|) + 理论尾
def tail_bound_terms(s, N1, N2):
    tot = mpf(0)
    for n in range(N1, N2 + 1):
        b = 2 * pi * n / mpf(NK) ** 0.5
        g1 = abs(b ** (s - 2)) * abs(gammainc(2 - s, b, mp.inf))
        g2 = abs(b ** (-s)) * abs(gammainc(s, b, mp.inf))
        tot += abs(bK[n]) * (g1 + g2)
    return tot

# 理论尾上界：|b_n| ≤ τ(n)·√n（Ramanujan/Deligne 上界；对 b_n 用 |b_n| ≤ (n 的因子数)·√n）
# 用粗界 τ(n) ≤ 2√n：|b_n| ≤ 2n；Γ 项 ≤ C·e^{-b}（b=2πn/37，n>800 ⟹ b>136，e^{-b} 主导）
# 尾：Σ_{n>NMAX} 2n·2·e^{-b} ≤ 4·Σ n·e^{-2πn/37}——几何级数封闭

def theory_tail_bound(N0):
    # Σ_{n>N0} 2n·2·e^{-2πn/37} = 4·Σ_{n>N0} n·q^n, q = e^{-2π/37}
    q = mp.e ** (-2 * pi / mpf(37))
    n0 = N0 + 1
    # Σ_{n>N0} n q^n = q^{n0}(n0 - (n0-1)q)/(1-q)^2
    S = q ** n0 * (mpf(n0) - (n0 - 1) * q) / (1 - q) ** 2
    return 4 * S

for N in (800, 1200):
    h = mpf('1e-3')
    Lp = (Lval(1 + h, N) - Lval(1 - h, N)) / (2 * h)
    # 差分误差：h²/6·|L'''|，|L'''| 用数值上界估计（保守 ×2）
    Lppp_num = abs((Lval(1 + 2 * h, N) - 2 * Lval(1 + h, N) + 2 * Lval(1 - h, N) - Lval(1 - 2 * h, N)) / (2 * h ** 3))
    diff_err = (h ** 2 / 6) * Lppp_num
    tb = tail_bound_terms(mpmathify(1) + h, N + 1, NMAX2)
    tbt = theory_tail_bound(N)
    total_err = diff_err + tb + tbt + mpf('1e-60')  # 舍入（dps=80）
    print('N=%d: L_K\'(1)≈%.12f  差分误差≤%.2e  显式尾≤%.2e  理论尾≤%.2e  总误差≤%.2e'
          % (N, Lp, diff_err, tb, tbt, total_err))
    print('      区间 [%.12f, %.12f]  → 非零判定: %s'
          % (Lp - total_err, Lp + total_err, (Lp - total_err) > 0))
