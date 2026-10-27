# -*- coding: utf-8 -*-
"""S2 数值定向 v3（entE_weil3.py）：逐 λ 分母 + 三构型对照。

构型自洽性（先验判定）：离线对 1/2±δ+iγ 同虚部（函数方程强制）⇒ 并集产生 d=0 极近对；
XXXVI 实测极近对(<1e-3)=0 ⇒ 威胁构型（同虚部成对）与实测间距结构冲突——数学自洽性排除优先于注入数值。

三种注入构型的 Weil 实部签名（x=e^λ，λ=log x，δ 深度，N_off 对）：
- P（物理加对，虚部集不变）：ΔP = −w_off + w_in（N_off 在线→N_off 对；总数+N_off，RvM 主项冲突）
  理论 SNR_P ≈ √(2N_off/N_K)·[2cosh(δλ)/(1+...)−1]≈√(2N_off/N_K)·(1+δ²λ²/2+O(δλ²/γ))（一阶主项=1）
- B（额外注入，非物理）：ΔB = −w_off；理论 SNR_B = √(2N_off/N_K)·cosh(δλ)
- C（总数守恒二阶：2N_off 在线等价→N_off 对，仅理论参考）：ΔC = −w_off + 2·w_in；理论 √(2N_off/N_K)(cosh(δλ)−1)
SNR[λ] = RMS_Δ[λ]/|R_on(λ)|（逐 λ，√x 因子消掉）；多抽样取 RMS。输出 entE_weil3.json。
"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))
N_K = len(G)
print("N_K =", N_K, flush=True)

LAM = np.arange(8.0, 40.5, 0.5)

def wsum(gamma_arr, delta, lam):
    e = np.exp(0.5 * lam + 1j * np.outer(gamma_arr, lam))
    if delta == 0.0:
        return np.sum(e / (0.5 + 1j * gamma_arr[:, None]), axis=0)
    return np.sum(e * (np.exp(-delta * lam) / (0.5 - delta + 1j * gamma_arr[:, None])
                       + np.exp(+delta * lam) / (0.5 + delta + 1j * gamma_arr[:, None])), axis=0)

print("基线…", flush=True)
R_on = -wsum(G, 0.0, LAM)
abs_on = np.abs(R_on)          # 逐 λ 基线幅度（√x 包络 × 游走）

rng = np.random.default_rng(20261024)
out = dict(N_K=N_K, lam=list(LAM))
rows = []
for delta in [0.01, 0.02, 0.05]:
    for N_off in [200, 2000, 2139, 50000, 219000]:
        if 2 * N_off > N_K:
            continue
        for gm in ["uniform", "low"]:
            reps = 6 if N_off >= 50000 else 10
            accP = np.zeros(len(LAM)); accB = np.zeros(len(LAM)); accC = np.zeros(len(LAM))
            for rep in range(reps):
                if gm == "uniform":
                    idx = rng.choice(N_K, size=N_off, replace=False)
                else:
                    iL = np.where(G < 2000.0)[0]
                    idx = rng.choice(iL, size=min(N_off, len(iL)), replace=False)
                gsel = G[idx]
                w_in = wsum(gsel, 0.0, LAM)
                w_off = wsum(gsel, delta, LAM)
                dP = -w_off + w_in
                dB = -w_off
                dC = -w_off + 2.0 * w_in
                accP += np.abs(dP) ** 2; accB += np.abs(dB) ** 2; accC += np.abs(dC) ** 2
            snrP = np.sqrt(accP / reps) / abs_on
            snrB = np.sqrt(accB / reps) / abs_on
            snrC = np.sqrt(accC / reps) / abs_on
            sq = np.sqrt(2.0 * N_off / N_K)
            k13 = int(np.argmin(np.abs(LAM - 13.3)))
            k30 = int(np.argmin(np.abs(LAM - 30.0)))
            row = dict(delta=delta, N_off=N_off, gm=gm,
                       P13=float(snrP[k13]), P30=float(snrP[k30]), Pmax=float(snrP.max()),
                       B13=float(snrB[k13]), Bmax=float(snrB.max()),
                       C13=float(snrC[k13]), C30=float(snrC[k30]), Cmax=float(snrC.max()),
                       theoP13=float(sq * (1.0 + 0.5 * (delta * 13.3) ** 2)),
                       theoC13=float(sq * (np.cosh(delta * 13.3) - 1.0)))
            rows.append(row)
            print("δ=%.2f N_off=%6d %-7s: P13=%.3f(P30=%.3f,pmax=%.3f) C13=%.3f(C30=%.3f,cmax=%.3f) | 理论P13=%.3f C13=%.3f"
                  % (delta, N_off, gm, row["P13"], row["P30"], row["Pmax"],
                     row["C13"], row["C30"], row["Cmax"], row["theoP13"], row["theoC13"]), flush=True)
out["rows"] = rows
out["runtime_s"] = time.time() - t0
with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entE_work\entE_weil3.json", "w", encoding="utf-8") as fp:
    json.dump(out, fp, ensure_ascii=False, indent=1)
print("SAVED entE_weil3.json %.0fs" % (time.time() - t0))
