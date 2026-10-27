# -*- coding: utf-8 -*-
"""S7 图：素数项层子指数可忽略性——χ_5 加权素数项轨迹 vs N_L 尺度 + SW 形态。
读 xlii_s7_prime.json，输出 xlii_s7_fig.png（英文标签）。"""
import json, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
d = json.load(open(os.path.join(QRH, "xlii_s7_prime.json"), encoding="utf-8"))

fig, axs = plt.subplots(1, 2, figsize=(11.5, 4.3), dpi=200)

# (a) |S(X)| 轨迹（两种 T 的核加权）vs N_L 尺度
ax = axs[0]
for T, r in d.items():
    Xs = r["sample_X"]
    S = np.abs(r["sample_S"])
    lab = "T=6e5 (weighted, |S|)" if T == "600000" else "T=8e5 (weighted, |S|)"
    ax.semilogx(Xs, S, "o-", lw=1.2, ms=3, label=lab)
ax.axhline(1e-2, color="crimson", ls="--", lw=1.0, label="10^-2 target (pairing scale)")
ax.set_xlabel("X (prime cutoff)")
ax.set_ylabel("|S(X)| = |sum Lambda*chi5*p^-1/2*Khat|")
ax.set_title("(a) prime term |S(X)| ~ O(10^-1) << 10^-2 target")
ax.grid(True, ls=":", alpha=0.5)
ax.legend(fontsize=8)

# (b) 未加权 S0（SW 振荡形态）
ax = axs[1]
r = d["600000"]
Xs = r["sample_X"]
S0 = r["sample_S0"]
ax.semilogx(Xs, S0, "s-", lw=1.2, ms=3, color="#1f4e79", label="S0=sum Lambda*chi5*p^-1/2 (unweighted)")
ax.axhline(0, color="k", lw=0.8)
ax.set_xlabel("X (prime cutoff)")
ax.set_ylabel("S0(X)")
ax.set_title("(b) SW form: bounded oscillation (|S0|<=2.9)")
ax.grid(True, ls=":", alpha=0.5)
ax.legend(fontsize=8)

fig.tight_layout()
out = os.path.join(QRH, "xlii_s7_fig.png")
fig.savefig(out)
print("saved:", out)
