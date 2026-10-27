# -*- coding: utf-8 -*-
"""S2 诊断：diff = (x−ψ_K(x)) − R_on(λ) 逐点形态（entE_weil_diag.py）"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))

Lmax = 200000
sieve = np.ones(Lmax + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(np.sqrt(Lmax)) + 1):
    if sieve[i]:
        sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.int64)
chi5 = {1: 1, 2: -1, 3: -1, 4: 1}
chi_p = np.array([chi5.get(int(p % 5), 0) for p in primes])

def psi_K_vals(xs):
    res = np.zeros(len(xs))
    for p, cp in zip(primes, chi_p):
        if p > xs[-1]:
            break
        pk = p; k = 1; lp = np.log(p)
        while pk <= xs[-1]:
            mask = xs >= pk
            res[mask] += lp
            if cp != 0:
                res[mask] += lp * (cp ** k)
            pk *= p; k += 1
    return res

LAMc = np.arange(8.0, 11.51, 0.5)
Xc = np.exp(LAMc).astype(np.int64)
psiK = psi_K_vals(Xc.astype(np.float64))
e = np.exp(0.5 * LAMc + 1j * np.outer(G, LAMc))
R_on = -np.sum(e / (0.5 + 1j * G[:, None]), axis=0)
diff = (Xc - psiK) - R_on.real
diff2 = (Xc - psiK) - 2.0 * R_on.real   # 共轭配对修正版
const = np.median(diff)
const2 = np.median(diff2)
resid = diff - const
resid2 = diff2 - const2
print("λ      x          ψK(x)      x−ψK      R_on.real   diff      resid   diff2    resid2")
for i, lam in enumerate(LAMc):
    print("%4.1f  %8d  %12.3f  %12.3f  %12.4f  %12.4f  %10.4f  %10.4f  %10.4f" %
          (lam, Xc[i], psiK[i], Xc[i]-psiK[i], R_on[i].real, diff[i], resid[i],
           diff2[i], resid2[i]))
print("const=%.4f resid_std=%.4f | const2=%.4f resid2_std=%.4f  R_on_std=%.4f" %
      (const, resid.std(), const2, resid2.std(), R_on.real.std()))
print("SAVED diag ok %.1fs" % (time.time()-t0))
