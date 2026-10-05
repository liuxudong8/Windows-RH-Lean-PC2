# -*- coding: utf-8 -*-
"""一致性核对：s=3 处 直接 Dirichlet 级数 vs Dokchitser 型延拓公式"""
import sys
sys.path.insert(0, r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA')
import importlib.util
spec = importlib.util.spec_from_file_location('skA_ext', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\skA_ext.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

from mpmath import mp, mpf, gammainc, gamma, pi
mp.dps = 50

NQ = 37
nmax = 800
coeffs = m.build_bn(nmax, m.ap_Q, {37}, 'ell')

# 直接 Dirichlet：L(3) = Σ a_n n^{-3}（收敛域）
s3 = mpf(3)
direct = mpf(0)
for n in range(1, nmax + 1):
    direct += coeffs[n] * (mpf(n) ** (-s3))

# 延拓公式
lam3 = m.Lambda(s3, coeffs, NQ, -1, nmax)
formula = (2 * pi / mpf(NQ) ** 0.5) ** s3 / gamma(s3) * lam3

print('L_dir(3)  =', direct)
print('L_fml(3)  =', formula)
print('ratio     =', formula / direct)

# 另查 w=+1 与 w=-1 在 s=3 的差
lam3p = m.Lambda(s3, coeffs, NQ, +1, nmax)
formulap = (2 * pi / mpf(NQ) ** 0.5) ** s3 / gamma(s3) * lam3p
print('L_fml(w=+1)(3) =', formulap)
