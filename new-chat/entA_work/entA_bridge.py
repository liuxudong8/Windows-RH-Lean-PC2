# -*- coding: utf-8 -*-
"""入口 A：显式公式余项桥——"离线且简单"定量（Stage 2 数值标定）

结构（Stage 1 框架）：
  全在线模型 psi_on（所有零点 sigma=1/2）：
      M_on(u) = Σ_γ e^{iuγ} / (1/2 + iγ),   u = log x
  真实 psi_K（离线零点 sigma=1/2−δ 贡献 x^ρ = x^{1/2} e^{-δu} 衰减）：
      M_pert(u) = Σ_on e^{iuγ}/(1/2+iγ) + Σ_off e^{iuγ} e^{-δu}/(1/2−δ+iγ)
  模型误差（离线导致的偏离）：
      B(u) = M_pert − M_on = Σ_off e^{iuγ} [ e^{-δu}/(1/2−δ+iγ) − 1/(1/2+iγ) ]
  相位随机近似：E|B(u)|² ≈ K·|e^{-δu}/(1/2−δ+iγ̄) − 1/(1/2+iγ̄)|² ≈ K·(δu)²/|1/2+iγ̄|²
  归一化余项 C_R = sup_u |M_on(u)| / sqrt(N)（自然余项幅度）
  余项桥（模型误差 ≤ 余项）：sqrt(N_off)·δ·λ ≤ C_R·sqrt(N)·c
      ⟹  N_off_max(δ) = (C_R·sqrt(N)·c/(δλ))² ，c 为允许倍数（数值标定）

Stage 2 输出：
  - 在线基线 M_on 的均方/sup（C_R 数值）
  - 扰动扫描 (K, δ)：实测 E|B|² 与理论 K·δ²u² 标度拟合，系数 c_obs
  - 反推 N_off_max(δ) 曲线，与目标带（λ₀=1.0: 0.1018·N_K≈21.9万；λ₀=0.74: ~200/430）对照
"""
import numpy as np, json, time, math
BASE = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_bridge.json"
t0 = time.time()
d = np.load(BASE + r"\zeros_T6e5.npz")
Z = np.sort(d["zeta"].astype(np.float64)); L = np.sort(d["L"].astype(np.float64))
T = 6e5; lam = np.log(T)
N_Z, N_L = len(Z), len(L); N_K = N_Z + N_L
GAM = np.concatenate([Z, L])           # 并集零点虚部（ζ_K）
# u 网格：u ∈ [3, λ+2]，λ=log T=13.3
U = np.linspace(3.0, lam + 2.0, 200)
NU = len(U)

# ---------- 在线基线 M_on ----------
def M_base(gamma, U):
    """M_on(u)=Σ e^{iuγ}/(1/2+iγ)，γ 为给定零点集（在线）。"""
    g = gamma.reshape(-1, 1)
    ph = np.exp(1j * g * U.reshape(1, -1))            # (N, NU)
    w = 1.0 / (0.5 + 1j * g)
    return (w.reshape(-1, 1) * ph).sum(axis=0)          # (NU,)

print("并集基线 M_on ...", flush=True)
M_on = M_base(GAM, U)
supM = float(np.max(np.abs(M_on)))
rmsM = float(np.sqrt(np.mean(np.abs(M_on) ** 2)))
C_R = supM / math.sqrt(N_K)                              # 归一化余项（sup 口径）
print("N_K=%d  sup|M_on|=%.2f  rms=%.2f  C_R=sup/sqrt(N)=%.4f" % (N_K, supM, rmsM, C_R), flush=True)

# ---------- 扰动扫描 ----------
rng = np.random.default_rng(20261023)
DELTAS = [0.005, 0.01, 0.02, 0.03, 0.05, 0.08, 0.10, 0.20, 0.40]
KS = [1000, 10000, 50000, 100000, 200000, 219000, 430000]
# 理论权重函数（相位随机近似，u 积分）
# 对固定 δ：每零点 E|B(u)|² 的 u-依赖 = |e^{-δu}/(1/2−δ+iγ) − 1/(1/2+iγ)|²，γ 平均取 √N 尺度参考
# 简化：E|B(u)|² ≈ K · wbar(δ,u)，wbar 由小样本零点子集数值标定

def B_vector(idx, delta, U):
    """扰动后 B(u)（只用离线子集 idx）。"""
    g = GAM[idx]
    e1 = np.exp(-delta * U.reshape(1, -1))
    ph = np.exp(1j * g.reshape(-1, 1) * U.reshape(1, -1))
    a = 1.0 / (0.5 - delta + 1j * g).reshape(-1, 1)
    b = 1.0 / (0.5 + 1j * g).reshape(-1, 1)
    return (ph * (e1 * a - b)).sum(axis=0)

# 预取各 δ 的 wbar（用 5000 零点子样本的平均单零点贡献，保证可复现）
SUB = rng.choice(N_K, size=5000, replace=False)
wbar_cache = {}
for delta in DELTAS:
    Bs = B_vector(SUB, delta, U)
    wbar_cache[delta] = float(np.mean(np.abs(Bs) ** 2) / len(SUB))

rows = []
for delta in DELTAS:
    wbar = wbar_cache[delta]
    for K in KS:
        idx = rng.choice(N_K, size=K, replace=False)
        B = B_vector(idx, delta, U)
        EB2 = float(np.mean(np.abs(B) ** 2))
        # 理论：K·wbar（相位随机、独立性）
        pred = K * wbar
        rows.append(dict(delta=delta, K=K, EB2=EB2, pred=pred, ratio=EB2 / pred,
                         supB=float(np.max(np.abs(B)))))
        print("δ=%.3f K=%7d  E|B|²=%12.4e  pred=%12.4e  ratio=%.3f  sup|B|=%.4f"
              % (delta, K, EB2, pred, ratio if False else EB2 / pred, float(np.max(np.abs(B)))))

# ---------- 反推 N_off_max(δ) ----------
# 模型误差均方 ≤ 允许预算：E|B|² ≤ (c·C_R·√N)²  ⟹  K ≤ c²·C_R²·N / wbar(δ)
# 取 c=1（偏差与自然余项同量级）与 c=C_R 档（严格）两个口径；另给 sup 口径 K_sup ≤ (c_s·C_R·√N/supB1)²
rows_inv = []
for delta in DELTAS:
    wbar = wbar_cache[delta]
    Kmax_c1 = (C_R * math.sqrt(N_K)) ** 2 / wbar
    Kmax_strict = (0.5 * C_R * math.sqrt(N_K)) ** 2 / wbar   # c=0.5
    rows_inv.append(dict(delta=delta, wbar=wbar,
                         Kmax_c1=Kmax_c1, Kmax_c05=Kmax_strict,
                         frac_N=Kmax_c1 / N_K))
    print("δ=%.3f  wbar=%.4e  N_off_max(c=1)=%.3e (%.4f·N)   c=0.5: %.3e"
          % (delta, wbar, Kmax_c1, Kmax_c1 / N_K, Kmax_strict))

GATE14 = 0.1018 * N_K     # λ₀=1.0 目标带（≈21.9万）
GATE074 = 430.0           # λ₀=0.74 目标带（审计口径~200/430）

out = dict(
    meta=dict(T=T, lam=lam, N_Z=N_Z, N_L=N_L, N_K=N_K, U_min=U[0], U_max=U[-1], nU=NU,
              supM=supM, rmsM=rmsM, C_R=C_R),
    deltas=DELTAS, Ks=KS,
    M_on_stats=dict(sup=supM, rms=rmsM, C_R=C_R),
    rows=rows, wbar_cache=wbar_cache, rows_inv=rows_inv,
    gates=dict(lam10=GATE14, lam074=GATE074),
    runtime_s=time.time() - t0)
with open(OUT, "w", encoding="utf-8") as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print("\nsaved", OUT, "%.1fs" % (time.time() - t0))
