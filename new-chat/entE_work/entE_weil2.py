# -*- coding: utf-8 -*-
"""S2 数值定向 v2：Weil 实部口径、正确威胁构型与 RMS 口径（entE_weil2.py）。

威胁构型（数据零点数守恒）：N_off 对离线零点（1/2±δ+iγ，同虚部）取代 2N_off 个在线零点。
- 构型 A''（取代）：ΔA = Σ_off对[离线对项 − 2×在线项(1/2+iγ)]——签名 (cosh(δλ)−1)≈δ²λ²/2（二阶）
- 构型 B（额外注入）：ΔB = Σ_off对[离线对项]——签名 cosh(δλ)（一阶，非物理：零点数变多）
理论（RMS 口径，均匀 γ 抽样）：SNR_A'' = √(2N_off/N_K)·(cosh(δλ)−1)、SNR_B = √(2N_off/N_K)·cosh(δλ)
λ 扫描放大：cosh(δλ)−1 ~ δ²λ²/2（λ² 增长）；γ 分布：均匀 vs 低 γ 集中（1/γ² 加权放大）。
输出：entE_weil2.json
"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))
N_K = len(G)
print("N_K =", N_K, flush=True)

LAM = np.arange(8.0, 40.5, 0.5)
X = np.exp(LAM)

def wsum(gamma_arr, delta, lam):
    """Σ x^ρ/ρ：delta=0 在线单零点；delta>0 离线对（1/2±δ+iγ）"""
    e = np.exp(0.5 * lam + 1j * np.outer(gamma_arr, lam))  # x^{1/2+iγ}
    if delta == 0.0:
        return np.sum(e / (0.5 + 1j * gamma_arr[:, None]), axis=0)
    return np.sum(e * (np.exp(-delta * lam) / (0.5 - delta + 1j * gamma_arr[:, None])
                       + np.exp(+delta * lam) / (0.5 + delta + 1j * gamma_arr[:, None])), axis=0)

print("基线 R_on…", flush=True)
R_on = -wsum(G, 0.0, LAM)   # 全在线基线（214 万）
rms_on = np.sqrt(np.mean(np.abs(R_on) ** 2))

rng = np.random.default_rng(20261024)
out = dict(N_K=N_K, lam=list(LAM), rms_on=float(rms_on))
rows = []
for delta in [0.01, 0.02, 0.05]:
    for N_off in [200, 2000, 2139, 50000, 219000]:
        if 2 * N_off > N_K:
            continue
        for gamma_mode in ["uniform", "low"]:
            reps = 6 if N_off >= 50000 else 10
            acc_A = np.zeros(len(LAM), dtype=float)
            acc_B = np.zeros(len(LAM), dtype=float)
            for rep in range(reps):
                if gamma_mode == "uniform":
                    idx = rng.choice(N_K, size=N_off, replace=False)
                else:  # 低 γ 集中：γ≤2000 内随机
                    lowmask = G < 2000.0
                    iL = np.where(lowmask)[0]
                    idx = rng.choice(iL, size=min(N_off, len(iL)), replace=False)
                gsel = G[idx]
                w_in = wsum(gsel, 0.0, LAM)       # 被取代的在线项（每 γ 一个）
                w_off = wsum(gsel, delta, LAM)     # 离线对项
                dA = -w_off + 2.0 * w_in           # 取代：离线对 vs 两在线等价（总数守恒）
                dB = -w_off                        # 额外注入
                acc_A += np.abs(dA) ** 2
                acc_B += np.abs(dB) ** 2
            rms_A = np.sqrt(acc_A / reps)
            rms_B = np.sqrt(acc_B / reps)
            snrA = rms_A / rms_on
            snrB = rms_B / rms_on
            theoA = np.sqrt(2.0 * N_off / N_K) * (np.cosh(delta * LAM) - 1.0)
            theoB = np.sqrt(2.0 * N_off / N_K) * np.cosh(delta * LAM)
            k13 = int(np.argmin(np.abs(LAM - 13.3)))
            rows.append(dict(delta=delta, N_off=N_off, gamma_mode=gamma_mode,
                             snrA_13=float(snrA[k13]), snrB_13=float(snrB[k13]),
                             theoA_13=float(theoA[k13]), theoB_13=float(theoB[k13]),
                             snrA_max=float(snrA.max()), snrB_max=float(snrB.max()),
                             snrA_30=float(snrA[int(np.argmin(np.abs(LAM-30.0)))])))
            print("δ=%.2f N_off=%6d %-6s: A13=%.3f(A30=%.3f,max=%.3f) B13=%.3f(max=%.3f) | 理论 A13=%.3f B13=%.3f"
                  % (delta, N_off, gamma_mode, snrA[k13], rows[-1]["snrA_30"], rows[-1]["snrA_max"],
                     snrB[k13], rows[-1]["snrB_max"], theoA[k13], theoB[k13]), flush=True)
out["rows"] = rows
out["runtime_s"] = time.time() - t0
with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entE_work\entE_weil2.json", "w", encoding="utf-8") as fp:
    json.dump(out, fp, ensure_ascii=False, indent=1)
print("SAVED entE_weil2.json %.0fs" % (time.time() - t0))
