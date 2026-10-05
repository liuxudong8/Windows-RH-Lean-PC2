# -*- coding: utf-8 -*-
"""决定性验证：Spicer Taylor 系数命题 b/a = η + log(2π/√N)
L_E(s+1) = s(a + bs + ...)，a = L'(1)，b = L''(1)/2
ℚ 端（N=37）与 K 端（N_K=1369）都验证。"""
import sys, importlib.util
from mpmath import mp, mpf, mpmathify, pi, euler, log
mp.dps = 30
spec = importlib.util.spec_from_file_location('m', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
eta = euler

def Lval(s, coeffs, N, w, nmax):
    return m.L(s, coeffs, N, w, nmax)

def Lprime1(coeffs, N, w, nmax, h=1e-4):
    return (Lval(mpmathify(1) + h, coeffs, N, w, nmax) - Lval(mpmathify(1) - h, coeffs, N, w, nmax)) / (2 * h)

def Lpp1(coeffs, N, w, nmax, h=1e-3):
    return (Lval(mpmathify(1) + h, coeffs, N, w, nmax) - 2 * Lval(mpmathify(1), coeffs, N, w, nmax)
            + Lval(mpmathify(1) - h, coeffs, N, w, nmax)) / (h * h)

def richardson(f, x0, h0, order=2):
    """Richardson 外推：f''(x0) 用 h0、h0/2 的差分外推"""
    def D2(h):
        return (f(x0 + h) - 2 * f(x0) + f(x0 - h)) / (h * h)
    d1 = D2(h0); d2 = D2(h0 / 2)
    return (4 * d2 - d1) / 3

nmax = 800
coeffsQ = m.build_bn(nmax, m.ap_Q, {37}, 'ell')
Lp = Lprime1(coeffsQ, 37, -1, nmax)
Lpp = Lpp1(coeffsQ, 37, -1, nmax)
Lpp_R = richardson(lambda s: Lval(s, coeffsQ, 37, -1, nmax), 1, 1e-3)
print('===== ℚ 端 37a1（N=37）=====')
print('L\'(1)      = %.10f' % Lp)
print('L\'\'(1)/2    = %.10f' % (Lpp / 2))
print('b/a (差分)  = %.10f' % (Lpp / (2 * Lp)))
print('b/a (Rich)  = %.10f' % (Lpp_R / (2 * Lp)))
target = eta + log(2 * pi / mpf(37) ** 0.5)
print('η + log(2π/√N) = %.10f   (差 %.2e)' % (target, Lpp_R / (2 * Lp) - target))

# K 端
print('===== K=ℚ(√5) 端（N_K=1369）=====')
nmaxK = 800
bK = [0] * (nmaxK + 1)
bK[1] = 1
split_tab, inert_tab, ram_tab = {}, {}, {}
for p in range(2, nmaxK + 1):
    isp = True; d = 2
    while d * d <= p:
        if p % d == 0:
            isp = False; break
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
LpK = Lprime1(bK, 1369, -1, nmaxK)
LppK_R = richardson(lambda s: Lval(s, bK, 1369, -1, nmaxK), 1, 1e-3)
print('L_K\'(1)    = %.10f' % LpK)
print('b/a (Rich) = %.10f' % (LppK_R / (2 * LpK)))
targetK = eta + log(2 * pi / mpf(1369) ** 0.5)
print('η + log(2π/√N_K) = %.10f   (差 %.2e)' % (targetK, LppK_R / (2 * LpK) - targetK))
