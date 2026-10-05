# -*- coding: utf-8 -*-
"""收敛展示：ℚ 端 LHS 随零点数 N 增加向 RHS 收缩"""
import sys, importlib.util
from mpmath import mp, mpf, mpmathify, pi, euler, log, sin, findroot
mp.dps = 30
spec = importlib.util.spec_from_file_location('m', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
eta = euler
nmax = 800
coeffsQ = m.build_bn(nmax, m.ap_Q, {37}, 'ell')
def Ls(s):
    return m.L(s, coeffsQ, 37, -1, nmax)
def von_Mangoldt(n):
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
def psi_E(x):
    tot = mpf(0)
    for n in range(2, int(x) + 1):
        a = coeffsQ[n]
        if a:
            tot += a * von_Mangoldt(n) / mpf(n)
    return -tot
def RHS(x, r_an=1):
    return (-eta - log(2 * pi / mpf(37) ** 0.5) - r_an * log(x)
            - log(1 - mpf(1) / x) + psi_E(x))
# 找零点到 tmax=32
zeros = []
t0 = 0.4; step = 0.05
prev = abs(Ls(mpmathify(1) + mp.j * mpmathify(t0)))
t = t0 + step
while t < 32:
    cur = abs(Ls(mpmathify(1) + mp.j * mpmathify(t)))
    if cur < 0.5 and cur < prev:
        try:
            sol = findroot(Ls, mpmathify(1) + mp.j * mpmathify(t), tol=1e-18)
            g = sol.imag
            if g > 0 and all(abs(g - zz) > 1e-4 for zz in zeros):
                zeros.append(g)
                print('γ ≈ %.8f' % g)
        except Exception:
            pass
    prev = cur; t += step
print('共 %d 个零点' % len(zeros))
for x in (2, 3, 5, 10):
    rhs = RHS(x)
    line = []
    for k in (4, 8, 14):
        zz = zeros[:k]
        lhs = sum(2 * sin(g * log(x)) / g for g in zz)
        line.append('N=%2d LHS=%+.6f' % (k, lhs))
    print('x=%2d  %s  |  RHS=%+.6f' % (x, '  '.join(line), rhs))
