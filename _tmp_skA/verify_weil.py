# -*- coding: utf-8 -*-
"""数值验证 Spicer 椭圆曲线显式公式（ℚ 端 37a1 与 K 端 base change）
Σ_{0<γ<T} 2sin(γ log x)/γ = −η − log(2π/√N) − r_an·log x − log(1−x⁻¹) + ψ_E(x)
ψ_E(x) = −Σ_{n≤x} a_n·Λ(n)/n （素幂 n）
"""
import sys, importlib.util
from mpmath import mp, mpf, mpmathify, pi, euler, log, sin
mp.dps = 30

spec = importlib.util.spec_from_file_location('m', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

eta = euler  # 0.57721566...

def von_Mangoldt(n):
    """Λ(n)：n = p^e 时为 log p，否则 0"""
    if n <= 1:
        return 0
    p = 2
    while p * p <= n:
        if n % p == 0:
            nn = n
            while nn % p == 0:
                nn //= p
            if nn == 1:
                return log(mpf(p))
            return 0
        p += 1
    return log(mpf(n))

def psi_E(x, coeffs):
    """ψ_E(x) = −Σ_{n≤x} a_n·Λ(n)/n"""
    tot = mpf(0)
    for n in range(2, int(x) + 1):
        a = coeffs[n]
        if a:
            tot += a * von_Mangoldt(n) / mpf(n)
    return -tot

def find_zeros(coeffs, N, w, nmax, tmax=25.0, nzeros=8):
    """找 L(s) 在临界线 Re s = 1 上的零点 γ（t ∈ (0, tmax]），排除中心 s=1。
    粗扫 |L|<0.5 局部极小 → findroot 复数精化。"""
    from mpmath import findroot
    def Ls(s):
        return m.L(s, coeffs, N, w, nmax)
    def Lval(t):
        return Ls(mpmathify(1) + mp.j * mpmathify(t))
    zeros = []
    t0 = 0.4
    step = 0.05
    prev = abs(Lval(t0))
    t = t0 + step
    while t < tmax and len(zeros) < nzeros:
        cur = abs(Lval(t))
        if cur < 0.5 and cur < prev:
            try:
                sol = findroot(Ls, mpmathify(1) + mp.j * mpmathify(t), tol=1e-20)
                g = sol.imag
                if g > 0 and all(abs(g - zz) > 1e-4 for zz in zeros):
                    zeros.append(g)
                    print('  零点 γ ≈ %.8f' % g)
            except Exception:
                pass
        prev = cur
        t += step
    return zeros

def tail_correction(zeros, x, tmax):
    """尾项估计：∫_T^∞ 2sin(γ log x)/γ · dN(γ)，dN/γ ~ (1/2π)log(γ/2πe)"""
    from mpmath import quad, pi, log as mlog, sin
    if not zeros:
        return mpf(0)
    T = max(zeros)
    L = mlog(x)
    return quad(lambda g: 2 * sin(g * L) / g * (mlog(g / (2 * pi * mp.e)) / (2 * pi)),
                [T, T + 1000], verbose=False)

def LHS(zeros, x, T=None):
    return sum(2 * sin(g * log(x)) / g for g in zeros)

def RHS(x, coeffs, N, r_an):
    return (-eta - log(2 * pi / mpf(N) ** 0.5) - r_an * log(x)
            - log(1 - mpf(1) / x) + psi_E(x, coeffs))

def check(zeros, x, coeffs, N, r_an):
    lhs = LHS(zeros, x)
    rhs = RHS(x, coeffs, N, r_an)
    tail = tail_correction(zeros, x, max(zeros))
    print('x=%5d  LHS(前%d零点)=%+.8f  +尾项%+.6f  RHS=%+.8f  diff(含尾)=%.2e'
          % (x, len(zeros), lhs, tail, rhs, lhs + tail - rhs))

# ---------- ℚ 端 37a1 ----------
print('===== ℚ 端 37a1（N=37，r_an=1）=====')
nmax = 1200
coeffsQ = m.build_bn(nmax, m.ap_Q, {37}, 'ell')
print('找零点：')
zerosQ = find_zeros(coeffsQ, 37, -1, nmax, tmax=25, nzeros=8)
for x in (2, 3, 5, 10):
    check(zerosQ, x, coeffsQ, 37, 1)

# ---------- K 端 base change ----------
print('===== K=ℚ(√5) 端（N_K=1369，r_an=1，b_n）=====')
nmaxK = 1200
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
print('找零点：')
zerosK = find_zeros(bK, 1369, -1, nmaxK, tmax=25, nzeros=8)
for x in (2, 3, 5, 10):
    check(zerosK, x, bK, 1369, 1)
