# -*- coding: utf-8 -*-
"""决定性最小复现：同一窗口（t≈450000）三口径对照 + 背景/峰分离"""
import numpy as np, json

T = 6e5; X = 300_000; EPS = 0.1
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
G = np.sort(np.concatenate([z["zeta"], z["L"]]))

C0, W = 450000.0, 50.0
gw = G[(G >= C0) & (G < C0 + W)]
print("窗口 [450000,450050] 零点数:", len(gw))

# ---- 口径 A：dt=0.02 精确背景 + 窗口内全峰，γ 最近网格点（窗口法原版）----
dtA = 0.02
tgA = np.arange(C0, C0 + W, dtA)
bgA = np.zeros(len(tgA))
for i0 in range(0, len(tgA), 4000):
    tb = tgA[i0:i0+4000]
    bgA[i0:i0+len(tb)] = np.real(a1 @ np.exp(-1j * np.outer(lp, tb)))
pkA = np.zeros(len(tgA))
for g in gw:
    pkA += EPS / (EPS*EPS + (tgA - g)**2)
hA = np.array([bgA[int(round((g-C0)/dtA))] + pkA[int(round((g-C0)/dtA))] for g in gw])
bg_at_A = np.array([bgA[int(round((g-C0)/dtA))] for g in gw])

# ---- 口径 C：dt=0.02 精确背景 + D=5 邻峰（γ 精确点）----
idx_lo = np.searchsorted(G, gw - 5.0); idx_hi = np.searchsorted(G, gw + 5.0)
pkC = np.full(len(gw), 1.0/EPS)
for k in range(len(gw)):
    seg = G[idx_lo[k]:idx_hi[k]]
    pkC[k] += np.sum(EPS / (EPS*EPS + (seg - gw[k])**2))
bgC = np.zeros(len(gw))
for i0 in range(0, len(gw), 2000):
    gb = gw[i0:i0+2000]
    bgC[i0:i0+len(gb)] = np.real(a1 @ np.exp(-1j * np.outer(lp, gb)))
hC = bgC + pkC

# ---- 口径 B：复用 entB_full.json 的全区间结果（插值背景+截断峰）----
full = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_full.json", encoding="utf-8"))
hB_mean_all = full["all"]["mean"]

# ---- 同点对照：插值 vs 精确（网格点）----
pts = np.arange(C0, C0 + W, 10.0)
bg_ex_pts = np.real(a1 @ np.exp(-1j * np.outer(lp, pts)))
tgB = np.arange(0.0, T + 0.2, 0.2)
bgB = np.zeros(len(tgB))
for i0 in range(0, len(tgB), 4000):
    tb = tgB[i0:i0+4000]
    bgB[i0:i0+len(tb)] = np.real(a1 @ np.exp(-1j * np.outer(lp, tb)))
bg_ip_pts = np.interp(pts, tgB, bgB)

out = dict(n=len(gw),
           A=dict(h_mean=float(hA.mean()), bg_mean=float(bg_at_A.mean()), pk_mean=float((hA-bg_at_A).mean())),
           C=dict(h_mean=float(hC.mean()), bg_mean=float(bgC.mean()), pk_mean=float(pkC.mean())),
           B_full_all=dict(h_mean=hB_mean_all),
           interp_check=dict(pts=pts.tolist(), bg_ex=bg_ex_pts.tolist(), bg_ip=bg_ip_pts.tolist(),
                             max_abs_diff=float(np.max(np.abs(bg_ex_pts - bg_ip_pts)))))
print("口径A(窗口法原版): ĥmean=%.3f  背景(γ处)=%.3f  峰=%.3f" % (hA.mean(), bg_at_A.mean(), (hA-bg_at_A).mean()))
print("口径C(精确bg+截断峰): ĥmean=%.3f  背景(γ处)=%.3f  峰=%.3f" % (hC.mean(), bgC.mean(), pkC.mean()))
print("口径B(插值bg+截断峰,全区间): ĥmean=%.3f" % hB_mean_all)
print("同点对照(网格点): max|插值−精确| = %.6f" % out["interp_check"]["max_abs_diff"])
json.dump(out, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_repro.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("saved entB_repro.json")
