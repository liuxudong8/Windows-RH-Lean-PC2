# -*- coding: utf-8 -*-
"""入口 B 实验四：全区间峰高实测（N_K=2149542 全部零点）

F(t=γ_i;ε) = 素项背景(γ_i) + Σ_{j:|γ_j−γ_i|≤D} ε/(ε²+(γ_i−γ_j)²)   [全在线模型，数据原样]

优化：
- 素项背景：粗网格 dt=0.2（特征频率 log p ≤ log 3e5=12.6 ⟹ Nyquist dt<0.25 ✓），分块矩阵乘，线性插值到零点
- 峰叠加：邻域截断 D=5（远峰贡献 ε/d²≤0.004，可忽略），分块向量化

产出：
- ĥ 全分布（ζ 族 / L 族分列）
- 左尾审计：ĥ<3 与 ĥ<1 计数（R-S 伪影的峰高签名：假零点处无峰 ⟹ ĥ≈背景）
- t 分箱均值剖面（伪影密度趋势 −0.0052/单位 的峰高表现）
- 反推：δ≥0.05 离线数量上界（2σ/3σ，用窗口法 Δh_off=2.92 标定）
"""
import numpy as np, json, time, math

t_start = time.time()
T = 6e5
X = 300_000
EPS = 0.1
DT_BG = 0.2
D_CUT = 5.0

def sieve(n):
    s = np.ones(n+1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
ps = sieve(X)
chi5 = np.where(ps % 5 == 0, 0, np.where((ps % 5 == 1) | (ps % 5 == 4), 1, -1))
a1 = (1.0 + chi5) * np.log(ps) / np.sqrt(ps) * np.exp(-EPS * np.log(ps))
lp = np.log(ps)
Np = len(ps)

z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
Zz = np.sort(z["zeta"]); ZL = np.sort(z["L"])
G = np.sort(np.concatenate([Zz, ZL]))
N_K = len(G)

# ---- 1. 素项背景粗网格（dt=0.2）----
tg = np.arange(0.0, T + DT_BG, DT_BG)
ng = len(tg)
bg = np.empty(ng, dtype=np.float64)
CHUNK = 5000
for i0 in range(0, ng, CHUNK):
    tb = tg[i0:i0+CHUNK]
    bg[i0:i0+len(tb)] = np.real(a1 @ np.exp(-1j * np.outer(lp, tb)))
t_bg = time.time()
print("背景粗网格: %d 点 × %d 素项 = %.1fs（%.3f/块）" % (ng, Np, t_bg - t_start, (t_bg-t_start)/ (ng/CHUNK)), flush=True)

bg_at = np.interp(G, tg, bg)

# ---- 2. 峰叠加（邻域截断 D_CUT；本峰由初始化 1/ε 计入一次，排除 d≈0 的自身/重复项）----
# 每零点本峰 1/ε + 邻峰 Σ ε/(ε²+d²)（|d|∈(1e-6, D_CUT]）；按 [start,end) 分块向量化
idx_lo = np.searchsorted(G, G - D_CUT)
idx_hi = np.searchsorted(G, G + D_CUT)   # [idx_lo[i], idx_hi[i]) 为邻域
peaks = np.full(N_K, 1.0 / EPS, dtype=np.float64)
BLK = 20000
for i0 in range(0, N_K, BLK):
    i1 = min(i0 + BLK, N_K)
    seg = G[i0:i1]
    lo = idx_lo[i0:i1].min(); hi = idx_hi[i1-1].max()
    gsub = G[lo:hi]
    # 邻域内所有对 (i in seg, j in gsub)，排除 |d|≤1e-6（自身/重复）
    d = gsub.reshape(1, -1) - seg.reshape(-1, 1)
    m = (np.abs(d) <= D_CUT) & (np.abs(d) > 1e-6)
    contrib = np.where(m, EPS / (EPS*EPS + d*d), 0.0).sum(axis=1)
    peaks[i0:i1] += contrib
t_peak = time.time()
print("峰叠加（邻域截断 D=%.0f）: %.1fs" % (D_CUT, t_peak - t_bg), flush=True)

h = bg_at + peaks

# ---- 3. 统计 ----
maskZ = np.isin(G, Zz)  # ζ 族标记（并集去重后按位置归属——近似：用值查找）
# 精确归属：G 来自 concat 排序，isin 可工作（浮点精确匹配）
hZ = h[maskZ]; hL = h[~maskZ]

def stats(arr, name):
    return dict(name=name, n=int(len(arr)), mean=float(arr.mean()), std=float(arr.std(ddof=1)),
                p1=float(np.percentile(arr, 1)), p50=float(np.percentile(arr, 50)),
                p99=float(np.percentile(arr, 99)), min=float(arr.min()), max=float(arr.max()),
                n_lt3=int(np.sum(arr < 3.0)), n_lt1=int(np.sum(arr < 1.0)))

# t 分箱剖面（100 箱）
bins = np.linspace(0, T, 101)
bi = np.digitize(G, bins) - 1
prof = []
for k in range(100):
    sel = bi == k
    if sel.sum():
        prof.append([float((bins[k]+bins[k+1])/2), float(h[sel].mean()), int(sel.sum())])
    else:
        prof.append([float((bins[k]+bins[k+1])/2), float("nan"), 0])

# 反推：δ≥0.05 离线数量上界（窗口法 Δh_off=2.92 实测标定；SE=std/√N）
std_all = float(h.std(ddof=1))
SE = std_all / math.sqrt(N_K)
DH_OFF = 2.92   # 窗口法实测：δ=0.05 单离线峰对均值的偏移
n_off_2s = 2.0 * SE / DH_OFF * N_K
n_off_3s = 3.0 * SE / DH_OFF * N_K

out = dict(meta=dict(T=T, X=X, EPS=EPS, Np=Np, N_K=N_K, n_zeta=int(len(Zz)), n_L=int(len(ZL)),
                     DT_BG=DT_BG, D_CUT=D_CUT),
           all=stats(h, "并集"), zeta=stats(hZ, "ζ 族"), L=stats(hL, "L 族"),
           profile=prof,
           infer=dict(std_all=std_all, SE=SE, DH_OFF=DH_OFF, n_off_2s=n_off_2s, n_off_3s=n_off_3s,
                      p_lim_2s=2.0*SE/DH_OFF, p_lim_3s=3.0*SE/DH_OFF),
           runtime_s=time.time() - t_start)
json.dump(out, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_full.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print("=== 全区间峰高实测 ===")
print("并集: n=%d mean=%.4f std=%.4f" % (out["all"]["n"], out["all"]["mean"], out["all"]["std"]))
print("ζ族: n=%d mean=%.4f std=%.4f ; L族: n=%d mean=%.4f std=%.4f"
      % (out["zeta"]["n"], out["zeta"]["mean"], out["zeta"]["std"], out["L"]["n"], out["L"]["mean"], out["L"]["std"]))
print("左尾 ĥ<3: 并集 %d（ζ %d / L %d）；ĥ<1: %d" % (out["all"]["n_lt3"], out["zeta"]["n_lt3"], out["L"]["n_lt3"], out["all"]["n_lt1"]))
print("反推: SE=%.5f, δ≥0.05 离线 N_off ≤ %.0f (2σ) / %.0f (3σ)" % (SE, n_off_2s, n_off_3s))
print("saved entB_full.json  %.1fs" % (time.time() - t_start))
