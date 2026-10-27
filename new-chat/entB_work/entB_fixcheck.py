# -*- coding: utf-8 -*-
"""修复验证：排除邻域内 d≈0（自身/重复）后，截断口径应与窗口法一致"""
import numpy as np

T = 6e5; X = 300_000; EPS = 0.1
def sieve(n):
    s = np.ones(n+1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
ps = sieve(X)
z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
G = np.sort(np.concatenate([z["zeta"], z["L"]]))

# 重复/极近 γ 计数（全局）
dG = np.diff(G)
print("全局: 重复 γ（间距=0）: %d ; 间距<1e-6: %d ; 间距<1e-3: %d" % (
    int(np.sum(dG == 0)), int(np.sum(dG < 1e-6)), int(np.sum(dG < 1e-3))))

C0, W = 450000.0, 50.0
gw = G[(G >= C0) & (G < C0 + W)]
idx_lo = np.searchsorted(G, gw - 5.0); idx_hi = np.searchsorted(G, gw + 5.0)
pk_fix = np.full(len(gw), 1.0/EPS)
pk_old = np.full(len(gw), 1.0/EPS)
for k in range(len(gw)):
    seg = G[idx_lo[k]:idx_hi[k]]
    d = seg - gw[k]
    pk_fix[k] += np.sum(np.where(np.abs(d) > 1e-6, EPS / (EPS*EPS + d*d), 0.0))   # 排除自身/重复
    pk_old[k] += np.sum(EPS / (EPS*EPS + d*d))                                     # 旧逻辑（含自身）
print("窗口 n=%d: 修复后峰 mean=%.3f（窗口法参考 17.53）| 旧逻辑峰 mean=%.3f | 差=%.3f"
      % (len(gw), pk_fix.mean(), pk_old.mean(), pk_old.mean() - pk_fix.mean()))
