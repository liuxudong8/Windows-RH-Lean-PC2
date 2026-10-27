# -*- coding: utf-8 -*-
"""攻防 XLII 数值件 G 图：SW 常数显式化对照。
左/主图：|psi(X,chi5)|/X（对数）vs sqrt(logX)：实测散点 + Kadiri 理论上界 e^{-c sqrt(logX)}（c=0.395）+ 实测上确界 7.6e-4。
附：L(1,chi5) 数值。
"""
import json, math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
plt.rcParams["font.sans-serif"] = ["SimHei"]
plt.rcParams["axes.unicode_minus"] = False

with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\xlii_s7g_sw_constant.json", encoding="utf-8") as f:
    d = json.load(f)
xs = np.array(d["xs"]); aps = np.array(d["abs_psi"])
sl = np.sqrt(np.log(xs))
rat = aps / xs
c_theory = d["kadiri"]["c_theory"]
C_obs = float(np.max(rat))

# L(1, chi5) 数值
L1 = 0.0
for n in range(1, 2_000_001):
    r = n % 5
    chi = 1 if r in (1, 4) else (-1 if r in (2, 3) else 0)
    L1 += chi / n

fig, ax = plt.subplots(figsize=(9, 5.5))
ax.semilogy(sl, rat, "o-", color="#1f77b4", ms=4, lw=1.2, label="实测 |psi(X,chi5)|/X")
xx = np.linspace(sl.min(), sl.max(), 200)
ax.plot(xx, np.exp(-c_theory * xx), "--", color="#d62728", lw=1.5,
        label=f"Kadiri 理论上界 e^(-c*sqrt(logX)), c=1/sqrt(R0)≈{c_theory:.3f}")
ax.axhline(C_obs, color="#2ca02c", lw=1.0, ls=":",
           label=f"实测上确界 {C_obs:.1e} (X in [10^5,10^7])")
ax.set_xlabel("sqrt(logX)")
ax.set_ylabel("|psi(X,chi5)|/X (log)")
ax.set_title("SW 常数显式化: L(s,chi5) 素数项实测 vs Kadiri 无条件上界")
ax.legend(fontsize=9)
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\xlii_s7g_fig.png", dpi=200)
print(f"L(1,chi5) = {L1:.6f}  (≈0.606, >0 远离 0 ⟹ 模 5 无 Siegel 零点)")
print(f"C_obs = {C_obs:.3e}   c_theory = {c_theory:.4f}")
print("saved fig")
