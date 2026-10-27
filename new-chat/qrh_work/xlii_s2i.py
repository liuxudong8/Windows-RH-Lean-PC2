# -*- coding: utf-8 -*-
"""S2(i) Weil 显式公式实部口径注入敏感性：N_off·δ²·(logx)² 累积可测性。

口径：归一化实部核 R(x) = Σ_γ [cos(γ log x)/2 + γ sin(γ log x)]/(1/4+γ²)
     = Σ_γ Re(x^{iγ}/ρ)/x^{1/2}（正虚部零点；成对因子 2 为公共常数，比例中消去）。
注入：把 N_off 个零点改为 β=1/2+δ（δ 偏移），核变为
     w^δ = x^δ [cos(γlogx)(1/2+δ) + γ sin(γlogx)]/((1/2+δ)²+γ²)
     Δ(x) = Σ_{γ∈N_off} (w^δ − w^0)
可测性：ρ₂(δ,N_off) = ⟨Δ²⟩_x / ⟨R²⟩_x（x 网格平均）。ρ₂≥1 ⟺ 注入效应 ≥ 基线。

解析预测（大 γ、随机相位）：⟨Δ²⟩ ~ N_off δ² (logx̄)² ⟨1/(2γ²)⟩_{N_off}，
基线 ⟨R²⟩ ~ Σ_all ⟨1/(2γ²)⟩，故 ρ₂ ~ N_off δ² (logx̄)² ⟨1/γ²⟩_{N_off} / (2·Σ_all⟨1/γ²⟩)。
"""
import json
import numpy as np

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\xlii_s2i.json"

d = np.load(NPZ)
gam = d["zeta"]                      # 正虚部零点（已过滤 [300,6e5]，999354 根）
gam = np.sort(gam)
N = gam.size
T = 6e5
logT = np.log(T)

# ---- x 网格（log x 口径）----
LX = np.linspace(4.0, 30.0, 27)     # log x ∈ [4,30]
lxbar = LX.mean()
logx = LX[None, :]                  # (1, n_x)

# ---- 基线核（β=1/2）----
# w0(γ,x) = [cos(γ lx)/2 + γ sin(γ lx)] / (1/4 + γ²)
g = gam[:, None]                    # (N,1)
w0 = (np.cos(g * logx) * 0.5 + g * np.sin(g * logx)) / (0.25 + g * g)
R2 = np.mean(np.sum(w0, axis=0) ** 2)          # 基线二矩 ⟨R²⟩_x
print("N=%d  logT=%.3f  baseline <R^2>_x = %.6e" % (N, logT, R2))

# ---- 注入核 w^δ ----
def delta_sum(idx, delta):
    gi = gam[idx, None]
    den = (0.5 + delta) ** 2 + gi * gi
    wd = (np.exp(delta * logx)) * (np.cos(gi * logx) * (0.5 + delta) + gi * np.sin(gi * logx)) / den
    wb = (np.cos(gi * logx) * 0.5 + gi * np.sin(gi * logx)) / (0.25 + gi * gi)
    return np.sum(wd - wb, axis=0)

def rel_second_moment(idx, delta):
    Dx = delta_sum(idx, delta)
    return np.mean(Dx ** 2) / R2

# ---- 扫描 ----
DELTAS = [0.01, 0.075, 0.1, 0.3]          # 0.075 = 1/logT（真实离线零点的最小尺度）
N_OFFS = [10, 100, 1000, 10000, 100000]

# 注入形态 (a) 最小 γ（左尾威胁，S1 224 审计延续）；(b) 随机（代表性）
rng = np.random.default_rng(20261024)
rand_idx = rng.permutation(N)
res = {"meta": {"T": T, "logT": round(logT, 4), "n_zeta": int(N),
                "lx_grid": [4.0, 30.0, 27], "baseline_R2": float(R2)},
       "matrix_min": {}, "matrix_rand": {}, "analytical": {}}

# 解析对照：Σ_all ⟨1/γ²⟩ 与 ⟨1/γ²⟩_{min-N_off}
inv2_all = np.sum(1.0 / gam ** 2)
print("analytic factor: 2*sum_all <1/g^2> = %.4e" % (2 * inv2_all))

for mode, idx_base in (("min", np.arange(N)), ("rand", rand_idx)):
    mat = {}
    for delta in DELTAS:
        row = {}
        for n_off in N_OFFS:
            idx = idx_base[:n_off]
            rho = rel_second_moment(idx, delta)
            row[str(n_off)] = round(rho, 4)
            inv2_off = np.sum(1.0 / gam[idx] ** 2)
            # 解析预测（γ 加权，随机相位）
            ana = n_off * delta ** 2 * lxbar ** 2 * inv2_off / (2 * inv2_all)
            print("%s  delta=%.3f  n_off=%d  rho2=%.4g  analytic=%.4g" % (mode, delta, n_off, rho, ana))
        mat[str(delta)] = row
    res["matrix_" + mode] = mat

# 边界：每 δ 的最小可测 N_off（ρ₂≥1，线性插值）
res["boundary"] = {}
for mode in ("min", "rand"):
    bd = {}
    for delta in DELTAS:
        mat = res["matrix_" + mode][str(delta)]
        nvals = np.array(N_OFFS, dtype=float); rvals = np.array([mat[str(n)] for n in N_OFFS])
        j = np.argmax(rvals >= 1.0)
        if rvals[j] >= 1.0:
            if j == 0:
                bd[str(delta)] = {"n_off_crit": round(nvals[0], 1), "rho2_at": float(rvals[0])}
            else:
                r0, r1 = rvals[j - 1], rvals[j]
                nc = nvals[j - 1] + (nvals[j] - nvals[j - 1]) * (1.0 - r0) / (r1 - r0)
                bd[str(delta)] = {"n_off_crit": round(nc, 1), "rho2_at": float(rvals[j])}
        else:
            bd[str(delta)] = {"n_off_crit": None, "rho2_at": float(rvals[-1])}
    res["boundary_" + mode] = bd

with open(OUT, "w", encoding="utf-8") as f:
    json.dump(res, f, ensure_ascii=False, indent=1)
print("saved:", OUT)
