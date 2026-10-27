# -*- coding: utf-8 -*-
"""S2 隔离诊断（entE_weil_diag2.py）：标准 ζ 的 ψ(x) vs x−2ReΣ（ζ族零点）。

若 ζ 部分吻合：R_on 求和/并集口径对；问题在 ψ_χ 侧。
若 ζ 部分也振荡：R_on 求和实现或零点数据问题。
ψ(x)=x−2ReΣ_{γ>0} x^ρ/ρ − log2π − (1/2)log(1−x⁻²)，ρ=1/2+iγ（ζ 族零点）。
"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
ZETA = np.sort(z["zeta"])

Lmax = 200000
sieve = np.ones(Lmax + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(np.sqrt(Lmax)) + 1):
    if sieve[i]:
        sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.int64)

def psi_vals(xs):
    res = np.zeros(len(xs))
    for p in primes:
        if p > xs[-1]:
            break
        pk = p; lp = np.log(p)
        while pk <= xs[-1]:
            res[xs >= pk] += lp
            pk *= p
    return res

LAMc = np.arange(8.0, 11.51, 0.5)
Xc = np.exp(LAMc).astype(np.int64)
psi = psi_vals(Xc.astype(np.float64))

e = np.exp(0.5 * LAMc + 1j * np.outer(ZETA, LAMc))
S = np.sum(e / (0.5 + 1j * ZETA[:, None]), axis=0)   # Σ x^ρ/ρ（单侧）
R = 2.0 * S.real                                      # 2ReΣ（对称配对零点项）
rhs = Xc.astype(np.float64) - R - np.log(2.0 * np.pi) - 0.5 * np.log(1.0 - Xc.astype(np.float64) ** -2)  # 显式公式右端（x 实）——x⁻²<1 ✓
diff = psi - rhs
print("λ      x          ψ(x)       x−2ReΣ−log2π   diff")
for i, lam in enumerate(LAMc):
    print("%4.1f  %8d  %12.4f  %12.4f  %12.5f" % (lam, Xc[i], psi[i], rhs[i], diff[i]))
print("diff_std=%.5f  (ψ 级 %.1f)" % (diff.std(), psi.std()))
print("SAVED diag2 ok %.1fs" % (time.time()-t0))
