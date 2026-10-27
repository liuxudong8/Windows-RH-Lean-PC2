# -*- coding: utf-8 -*-
"""诊断：全区间插值口径 vs 窗口法精确口径（同 t 区段对照）"""
import numpy as np, json, math

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

# 三个诊断区段
SEGS = [(0.0, 6000.0), (150000.0, 156000.0), (450000.0, 456000.0)]
out = {}
for (t0, t1) in SEGS:
    gw = G[(G >= t0) & (G < t1)]
    # 精确口径：dt=0.02 网格背景（分块）+ 窗口内峰叠加，γ 最近点
    tg = np.arange(t0, t1, 0.02)
    bg_ex = np.zeros(len(tg))
    for i0 in range(0, len(tg), 5000):
        tb = tg[i0:i0+5000]
        bg_ex[i0:i0+len(tb)] = np.real(a1 @ np.exp(-1j * np.outer(lp, tb)))
    pe = np.zeros(len(tg))
    for g in gw:
        pe += EPS / (EPS*EPS + (tg - g)**2)
    F_ex = bg_ex + pe
    h_ex = np.array([F_ex[int(round((g - t0)/0.02))] for g in gw])
    # 插值口径：dt=0.2 背景（分块）+ D=5 邻峰（复刻 entB_full 逻辑）
    tg2 = np.arange(0.0, T + 0.2, 0.2)
    bg2 = np.zeros(len(tg2))
    for i0 in range(0, len(tg2), 5000):
        tb = tg2[i0:i0+5000]
        bg2[i0:i0+len(tb)] = np.real(a1 @ np.exp(-1j * np.outer(lp, tb)))
    bg_at = np.interp(gw, tg2, bg2)
    idx_lo = np.searchsorted(G, gw - 5.0)
    idx_hi = np.searchsorted(G, gw + 5.0)
    pk = np.full(len(gw), 1.0/EPS)
    for k in range(len(gw)):
        seg = G[idx_lo[k]:idx_hi[k]]
        pk[k] += np.sum(EPS / (EPS*EPS + (seg - gw[k])**2))
    h_ip = bg_at + pk
    out[str((t0, t1))] = dict(n=len(gw),
                              ex_mean=float(h_ex.mean()), ex_std=float(h_ex.std(ddof=1)),
                              ip_mean=float(h_ip.mean()), ip_std=float(h_ip.std(ddof=1)),
                              bg_ex_mean=float(bg_ex.mean()), bg_ip_mean=float(bg_at.mean()))
    print("区段 [%.0f,%.0f] n=%d  精确 mean=%.3f std=%.3f | 插值 mean=%.3f std=%.3f | 背景: 精确 %.3f / 插值 %.3f"
          % (t0, t1, len(gw), h_ex.mean(), h_ex.std(ddof=1), h_ip.mean(), h_ip.std(ddof=1),
             bg_ex.mean(), bg_at.mean()), flush=True)

json.dump(out, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_diag.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("saved entB_diag.json")
