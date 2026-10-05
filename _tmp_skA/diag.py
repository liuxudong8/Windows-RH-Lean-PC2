# -*- coding: utf-8 -*-
"""逐项诊断 Λ(3)：直接定义式 vs 反射公式"""
import sys, importlib.util
from mpmath import mp, mpf, gammainc, gamma, pi
mp.dps = 50
spec = importlib.util.spec_from_file_location('skA_ext', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

N = 37
nmax = 800
coeffs = m.build_bn(nmax, m.ap_Q, {37}, 'ell')
s3 = mpf(3)
sqN = mpf(N) ** 0.5

# 直接项：Λ(3)_n = a_n (√N/2π)^3 Γ(3) n^{-3}
true_lam = mpf(0)
# 反射项：a_n[ε·Γ(2-3,b)+Γ(3,b)]，ε=-1
refl_lam = mpf(0)
for n in range(1, nmax + 1):
    a = coeffs[n]
    bn = 2 * pi * n / sqN
    t_true = a * (sqN / (2 * pi)) ** 3 * gamma(3) * (mpf(n) ** (-3))
    t_refl = a * (-1 * gammainc(-1, bn, mp.inf) + gammainc(3, bn, mp.inf))
    true_lam += t_true
    refl_lam += t_refl

print('Λ_dir(3)  =', true_lam)
print('Λ_refl(3) =', refl_lam)
print('L_refl(3) =', refl_lam * (2 * pi / sqN) ** 3 / gamma(3))

# 单项检查 n=1
n = 1
a = coeffs[1]
bn = 2 * pi * 1 / sqN
print('b_1 =', bn)
print('Γ(-1,b)  =', gammainc(-1, bn, mp.inf))
print('Γ(3,b)   =', gammainc(3, bn, mp.inf))
print('真值项 Λ(3)_1 =', a * (sqN / (2 * pi)) ** 3 * gamma(3))
print('反射项 Λ(3)_1 =', a * (-gammainc(-1, bn, mp.inf) + gammainc(3, bn, mp.inf)))
