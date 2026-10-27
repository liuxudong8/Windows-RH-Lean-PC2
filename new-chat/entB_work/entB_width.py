# -*- coding: utf-8 -*-
"""入口 B 实验三：威胁窗峰高测量数值定向（统计平均口径）

F(t;ε) = Re[−(ζ_K′/ζ_K)(1/2+ε+it)] = 素项背景 + Σ_ρ (ε+δ_ρ)/((ε+δ_ρ)²+(t−γ)²)
在线峰高 h=1/ε；离线峰（深度 δ）h=1/(ε+δ) —— 高度差 Δh=1/ε−1/(ε+δ)

不要求单峰可辨（SNR~1.8），用统计平均：测 N 个峰的 ĥ，混合 p 比例离线后
均值偏移 p·Δh，标准误 σ_ĥ/√N ⟹ 检测 σ = p·Δh·√N/σ_ĥ。

场景：
  (a) 全在线（数据原样，R-S 假设）
  (b) 合成：窗口内随机 p 比例零点移至深度 δ（峰宽 ε+δ）
参数网格：δ∈{0.05,0.07,0.09} × p∈{0.02,0.05,0.1}
素项背景每窗口算一次缓存；峰叠加分场景。

输出：检测 σ 表 + 全区间外推（N=2.15e6 的 σ_lim）。
"""
import numpy as np, json, time, math

t_start = time.time()
T = 6e5
X = 300_000                    # 素数表
EPS = 0.1
W = 50.0                       # 窗口宽
DT = 0.02                      # t 网格步长
M_WIN = 100                    # 窗口数
SEED = 7

def sieve(n):
    s = np.ones(n+1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
ps = sieve(X)
chi5 = np.where(ps % 5 == 0, 0, np.where((ps % 5 == 1) | (ps % 5 == 4), 1, -1))
a1 = (1.0 + chi5) * np.log(ps) / np.sqrt(ps) * np.exp(-EPS * np.log(ps))
lp = np.log(ps)

z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))     # 并集零点虚部
N_K = len(G)

rng = np.random.default_rng(SEED)
# 随机窗口中心（避开两端）
lo, hi = 200.0, T - 300.0
centers = rng.uniform(lo, hi, M_WIN)

def prime_bg(tgrid):
    """素项背景 Re Σ a_p p^{−1/2−ε−it}（分块）"""
    out = np.zeros(len(tgrid))
    for i in range(0, len(tgrid), 4000):
        tb = tgrid[i:i+4000]
        out[i:i+4000] = np.real(a1 @ np.exp(-1j * np.outer(lp, tb)))
    return out

def peak_sum(tgrid, gammas, dc):
    """峰叠加：Σ dc/(dc²+(t−γ)²)，dc=峰宽参数（ε 或 ε+δ）"""
    tt = tgrid.reshape(1, -1)
    g = gammas.reshape(-1, 1)
    return (dc / (dc*dc + (tt - g)**2)).sum(axis=0)

# 每窗口：素项背景 + 窗口内零点的在线峰（场景 a 基线）
bg_cache, peaks_on = [], []
win_g = []
for c in centers:
    tg = np.arange(c, c + W, DT)
    bg_cache.append(prime_bg(tg))
    gw = G[(G >= c) & (G < c + W)]
    win_g.append(gw)
    peaks_on.append(peak_sum(tg, gw, EPS))

# 场景 (a)：ĥ₀ = 素项背景 + 在线峰，在 γ 处取值
h0 = []
for i in range(M_WIN):
    F = bg_cache[i] + peaks_on[i]
    nF = len(F)
    for g in win_g[i]:
        j = int(round((g - centers[i]) / DT))
        h0.append(F[min(j, nF - 1)])
h0 = np.array(h0)
N0 = len(h0)
mean0, std0 = float(h0.mean()), float(h0.std(ddof=1))

# 场景 (b)：合成离线（δ、p 网格）
DELTAS = [0.05, 0.07, 0.09]
PS = [0.02, 0.05, 0.10]
res = {}
for d in DELTAS:
    for p in PS:
        hs = []
        rng2 = np.random.default_rng(SEED * 1000 + int(d * 1000) + int(p * 100))
        for i in range(M_WIN):
            gw = win_g[i]
            tg = np.arange(centers[i], centers[i] + W, DT)
            k_off = max(1, int(round(p * len(gw))))
            off_idx = rng2.choice(len(gw), size=k_off, replace=False)
            off = gw[off_idx]
            F = bg_cache[i] + peak_sum(tg, gw, EPS) \
                + (peak_sum(tg, off, EPS + d) - peak_sum(tg, off, EPS))
            nF = len(F)
            for g in gw:
                j = int(round((g - centers[i]) / DT))
                hs.append(F[min(j, nF - 1)])
        hs = np.array(hs)
        diff = float(hs.mean() - mean0)
        se = std0 / math.sqrt(len(hs))
        sigma = diff / se
        res["d%.2f_p%.2f" % (d, p)] = dict(delta=d, p=p, n=len(hs),
                                           mean=float(hs.mean()), diff=diff, se=se, sigma=sigma)

# 全区间外推（N=N_K 全部峰）：σ_lim = p·Δh·√N_K/σ_ĥ
rows_extrap = []
for d in DELTAS:
    dh = 1.0/EPS - 1.0/(EPS + d)
    for p in PS:
        s_lim = p * dh * math.sqrt(N_K) / std0
        rows_extrap.append(dict(delta=d, p=p, sigma_lim=s_lim))

out = dict(meta=dict(T=T, X=X, EPS=EPS, W=W, DT=DT, M_WIN=M_WIN, N_K=N_K, N0=N0,
                     mean0=mean0, std0=std0, n_win_avg=[len(g) for g in win_g][:3]),
           res=res, extrap=rows_extrap,
           note="σ=均值偏移/标准误；全区间外推 σ_lim=p·Δh·√N_K/σ_ĥ（窗口法 N=%.0f 的外推）" % N0)
json.dump(out, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_width.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)

print("=== 基线（场景 a，全在线）===")
print("N0=%d 峰，ĥ 均值=%.4f（理论 1/ε=10），std=%.4f" % (N0, mean0, std0))
print("=== 合成离线检测 σ（窗口法，N≈%d）===" % N0)
for k, v in res.items():
    print("δ=%.2f p=%.2f: 均值偏移=%.4f  SE=%.4f  检测σ=%.2f" % (v["delta"], v["p"], v["diff"], v["se"], v["sigma"]))
print("=== 全区间外推（N=2.15e6）===")
for r in rows_extrap:
    print("δ=%.2f p=%.2f: σ_lim=%.1f" % (r["delta"], r["p"], r["sigma_lim"]))
print("saved entB_width.json  %.1fs" % (time.time() - t_start))
