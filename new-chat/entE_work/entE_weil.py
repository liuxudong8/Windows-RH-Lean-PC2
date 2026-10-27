# -*- coding: utf-8 -*-
"""S2 数值定向：Weil 显式公式实部口径的离线注入敏感性（entE_weil.py，可复跑）。

对象：Weil 显式公式零点项 R(λ)=−Σ_ρ x^ρ/ρ（x=e^λ，λ=log x；常数项对注入不变，差分消掉）。
离线零点对（1/2−δ+iγ, 1/2+δ+iγ）成对贡献 √x·cosh(δλ)·e^{iγλ}/γ 级——相对在线基线偏差 cosh(δλ)−1≈δ²λ²/2（δ 一阶消失）。
理论预测：SNR ≈ √(N_off/N_on)·δ²λ²/2（随机相位 RMS 口径，√x 消掉）。

数值实验：
- 基线 R_on(λ)：并集 214 万零点全在线
- 注入构型 A（取代）：随机 N_off 个在线零点 → 替换为离线对（总数不变；ΔA = 替换差值）
- 注入构型 B（注入）：在线和 + N_off 个离线对（总数多 2N_off；ΔB = 新增差值）
- λ 网格 8..40；SNR=|Δ|/|R_on| 与理论 √(N_off/N_on)·δ²λ²/2 对照
- 多次随机抽样取期望（相位去运气）
输出：entE_weil.json
"""
import numpy as np, json, time

t0 = time.time()
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))
N_K = len(G)
print("N_K =", N_K, flush=True)

LAM = np.arange(8.0, 40.5, 0.5)
X = np.exp(LAM)

def weil_term(gamma_arr, delta, lam):
    """Σ x^ρ/ρ：ρ=1/2±δ+iγ（delta 为 0=在线、>0=离线对求和）"""
    g = gamma_arr
    L = lam
    e = np.exp(0.5 * L + 1j * np.outer(g, L))  # x^{1/2+iγ}
    if delta == 0.0:
        return np.sum(e / (0.5 + 1j * g[:, None]), axis=0)
    # 离线对：ρ±=1/2±δ+iγ（同虚部）
    e_lo = e * np.exp(-delta * L)               # x^{1/2−δ+iγ}
    e_hi = e * np.exp(+delta * L)               # x^{1/2+δ+iγ}
    rho_lo = 0.5 - delta + 1j * g[:, None]
    rho_hi = 0.5 + delta + 1j * g[:, None]
    return np.sum(e_lo / rho_lo + e_hi / rho_hi, axis=0)

print("基线 R_on 计算…", flush=True)
R_on = -weil_term(G, 0.0, LAM)

rng = np.random.default_rng(20261024)
GRID = [("N_off", [200, 2000, 2139, 50000, 219000]),
        ("delta", [0.01, 0.02, 0.05])]

res = dict(N_K=N_K, lam=list(LAM), R_on_abs=[float(abs(v)) for v in R_on])
rows = []
for delta in [0.01, 0.02, 0.05]:
    for N_off in [200, 2000, 2139, 50000, 219000]:
        if N_off > N_K // 2:
            continue
        # 多次随机抽样
        snr_max = 0.0; snr_at13 = 0.0
        reps = 4 if N_off >= 50000 else 8
        for rep in range(reps):
            idx = rng.choice(N_K, size=N_off, replace=False)
            gsel = G[idx]
            # 构型 A（取代）：在线和 − 选中零点项 + 离线对
            R_sel = -weil_term(gsel, 0.0, LAM)
            R_off = -weil_term(gsel, delta, LAM)
            dA = R_off - R_sel   # 取代差值
            # 构型 B（注入）：在线和 + 离线对（额外）
            dB = -weil_term(gsel, delta, LAM)
            # SNR 用 |Δ|/|R_on|
            sA = np.abs(dA) / np.abs(R_on)
            sB = np.abs(dB) / np.abs(R_on)
            snr_max = max(snr_max, float(sA.max()), float(sB.max()))
            k13 = int(np.argmin(np.abs(LAM - 13.3)))
            snr_at13 = max(snr_at13, float(sA[k13]), float(sB[k13]))
        theo = np.sqrt(N_off / N_K) * (delta * delta * 13.305 * 13.305 / 2.0)
        rows.append(dict(delta=delta, N_off=N_off, snr_max=snr_max, snr_at13=snr_at13,
                         theo_at13=theo))
        print("δ=%.2f N_off=%6d: SNR@13=%.4f（理论 %.4f） max=%.4f"
              % (delta, N_off, snr_at13, theo, snr_max), flush=True)

res["rows"] = rows
res["runtime_s"] = time.time() - t0
with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entE_work\entE_weil.json", "w", encoding="utf-8") as fp:
    json.dump(res, fp, ensure_ascii=False, indent=1)
print("SAVED entE_weil.json %.0fs" % (time.time() - t0))
