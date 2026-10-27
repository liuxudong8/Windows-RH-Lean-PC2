# -*- coding: utf-8 -*-
"""S2 正式校验（entE_weil_check2.py）：ψ_K(x) 素数侧 vs Weil 零点侧（正确符号）。

ψ_K(x)=ψ(x)+ψ_χ₅(x)；显式公式 ψ_K(x)=x+2·ReΣ_{γ>0} x^ρ/ρ + c_K（零点项实数 = −Σ_{γ≠0}=−2ReΣ_{γ>0}；
R_on=−Σ_{γ>0} x^ρ/ρ ⇒ 零点项 = 2·R_on.real）。
差分口径：diff = (x−ψ_K) + 2·R_on.real 应 ≈ 常数 c_K（±截断小项）。
x=e^λ、λ∈[8,11.5]（x≤1e5≪T=6e5，截断误差 (x·log²x)/T≤~12 可控）。
输出 entE_weil_check2.json。
"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))
N_K = len(G)

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

LAMc = np.arange(8.0, 11.51, 0.25)
Xc = np.exp(LAMc).astype(np.int64)
psiK = psi_K_vals(Xc.astype(np.float64))
e = np.exp(0.5 * LAMc + 1j * np.outer(G, LAMc))
R_on = -np.sum(e / (0.5 + 1j * G[:, None]), axis=0)
diff = (Xc.astype(np.float64) - psiK) + 2.0 * R_on.real
const = np.median(diff)
resid = diff - const
print("const=%.4f  resid: max=%.4f std=%.4f | R_on.real std=%.4f  psiK std=%.1f" %
      (const, np.abs(resid).max(), resid.std(), R_on.real.std(), psiK.std()), flush=True)
out = dict(N_K=N_K, lam=list(LAMc), const=float(const),
           resid_max=float(np.abs(resid).max()), resid_std=float(resid.std()),
           ratio_resid_on=float(resid.std() / R_on.real.std()),
           psiK=[float(v) for v in psiK], R_on_real=[float(v) for v in R_on.real])
with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entE_work\entE_weil_check2.json", "w", encoding="utf-8") as fp:
    json.dump(out, fp, ensure_ascii=False, indent=1)
print("SAVED entE_weil_check2.json %.0fs" % (time.time() - t0))
