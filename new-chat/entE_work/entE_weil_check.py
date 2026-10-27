# -*- coding: utf-8 -*-
"""S2 实现校验（entE_weil_check.py）：真实 ψ_K(x)（素数侧） vs Weil 零点侧 R_on。

ψ_K(x)=ψ(x)+ψ_χ₅(x)：ψ(x)=Σ_{p^k≤x}log p；ψ_χ₅(x)=Σ_{p^k≤x}χ₅(p)^k·log p，χ₅(1,2,3,4)=(1,−1,−1,1)。
Weil 显式公式：ψ_K(x)=x−Σ_ρ x^ρ/ρ−c_K（c_K 常数；极点项并入常数）——差分口径：R_on(λ)=−Σ_ρ x^ρ/ρ（γ≤T 截断）与 x−ψ_K(x) 差应 ≈ 常数 + 截断小项。
x=e^λ、λ∈[8,13.5]（x≤7.3e5 ≤ 筛上限 8e5）。输出 entE_weil_check.json。
"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))
N_K = len(G)

# 埃筛到 8e5
Lmax = 800000
sieve = np.ones(Lmax + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(np.sqrt(Lmax)) + 1):
    if sieve[i]:
        sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.int64)
print("primes ≤%d: %d" % (Lmax, len(primes)), flush=True)

chi5 = {1: 1, 2: -1, 3: -1, 4: 1}
def psi_K_vals(xs):
    """ψ_K(x) 逐 x（素数幂和，χ₅ 调制）"""
    res = np.zeros(len(xs))
    pm = primes % 5
    chi_p = np.array([chi5.get(int(p % 5), 0) for p in primes])
    for p, cp in zip(primes, chi_p):
        if p > xs[-1]:
            break
        pk = p; k = 1; lp = np.log(p)
        while pk <= xs[-1]:
            mask = xs >= pk
            res[mask] += lp
            if cp != 0:
                res[mask] += lp * (cp ** k)   # χ₅(p)^k（k=1 时 χ₅(p)；k 偶 χ=1 已并入主项？——标准：ψ_χ=Σχ(p^k)logp——χ(p^k)=χ(p)^k）
            pk *= p; k += 1
    return res

LAMc = np.arange(8.0, 11.51, 0.25)
Xc = np.exp(LAMc).astype(np.int64)
print("ψ_K(x) 素数侧…", flush=True)
psiK = psi_K_vals(Xc.astype(np.float64))

# Weil 零点侧：R_on(λ) = −Σ x^ρ/ρ（γ≤6e5 截断）
e = np.exp(0.5 * LAMc + 1j * np.outer(G, LAMc))
R_on = -np.sum(e / (0.5 + 1j * G[:, None]), axis=0)
R_on_real = R_on.real

# 差分：x − ψ_K(x) vs R_on_real——差应为常数（±截断小项）
diff = (Xc - psiK) - R_on_real
const = np.median(diff)
resid = diff - const
print("const=%.4f  resid: max|.|=%.4f  std=%.4f  (相对 |R_on|: %.3f)" %
      (const, np.abs(resid).max(), np.std(resid), np.std(resid) / np.std(R_on_real)), flush=True)
out = dict(N_K=N_K, lam=list(LAMc), const=float(const),
           resid_max=float(np.abs(resid).max()), resid_std=float(np.std(resid)),
           ratio=float(np.std(resid) / np.std(R_on_real)),
           psiK=[float(v) for v in psiK], R_on_real=[float(v) for v in R_on_real])
with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entE_work\entE_weil_check.json", "w", encoding="utf-8") as fp:
    json.dump(out, fp, ensure_ascii=False, indent=1)
print("SAVED entE_weil_check.json %.0fs" % (time.time() - t0))
