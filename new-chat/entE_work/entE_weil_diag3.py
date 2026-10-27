# -*- coding: utf-8 -*-
"""S2 隔离诊断3（entE_weil_diag3.py）：ψ_χ₅(x)（素数侧 χ 加权） vs −2ReΣ_{L族零点}。

差分口径：diff_χ = ψ_χ(x) + 2ReΣ_{L族} 应 ≈ 常数 c_χ（L 显式公式常数，含 (1/2)log(1−x⁻²)·阶数 0）。
ψ_χ(x)=Σ_{p^k≤x}χ₅(p)^k·log p；χ₅(1,2,3,4)=(1,−1,−1,1)、χ₅(0)=0。
"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
LZ = np.sort(z["L"])

Lmax = 200000
sieve = np.ones(Lmax + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(np.sqrt(Lmax)) + 1):
    if sieve[i]:
        sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.int64)
chi5 = {1: 1, 2: -1, 3: -1, 4: 1}
chi_p = np.array([chi5.get(int(p % 5), 0) for p in primes])

def psi_chi_vals(xs):
    res = np.zeros(len(xs))
    for p, cp in zip(primes, chi_p):
        if p > xs[-1]:
            break
        pk = p; k = 1; lp = np.log(p)
        while pk <= xs[-1]:
            if cp != 0:
                res[xs >= pk] += lp * (cp ** k)
            pk *= p; k += 1
    return res

LAMc = np.arange(8.0, 11.51, 0.5)
Xc = np.exp(LAMc).astype(np.int64)
psichi = psi_chi_vals(Xc.astype(np.float64))
e = np.exp(0.5 * LAMc + 1j * np.outer(LZ, LAMc))
S_L = np.sum(e / (0.5 + 1j * LZ[:, None]), axis=0)
diff = psichi + 2.0 * S_L.real
print("λ      x          ψ_χ(x)    2ReΣ_L      diff")
for i, lam in enumerate(LAMc):
    print("%4.1f  %8d  %12.4f  %12.4f  %12.5f" % (lam, Xc[i], psichi[i], 2.0*S_L[i].real, diff[i]))
print("diff_std=%.5f  ψ_χ std=%.1f  2ReΣ_L std=%.1f" % (diff.std(), psichi.std(), (2.0*S_L.real).std()))
print("SAVED diag3 ok %.1fs" % (time.time()-t0))
