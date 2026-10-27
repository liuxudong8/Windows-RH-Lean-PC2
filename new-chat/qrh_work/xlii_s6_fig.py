# -*- coding: utf-8 -*-
"""S6 图：λ_eff≤1 卡点解决——λ≤1/2 最优核族配对常数剖面 + ε 逼近 + 分解口径在线比例。
读 xlii_s6_lambda.json，输出 xlii_s6_fig.png（英文标签）。"""
import json, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
d = json.load(open(os.path.join(QRH, "xlii_s6_lambda.json"), encoding="utf-8"))
CMT = d["C_MT"]

fig, axs = plt.subplots(1, 3, figsize=(15.5, 4.6), dpi=200)

# (a) λ≤1/2 域 A 剖面（λ 尺度族）+ C_MT 线
ax = axs[0]
for k, r in d["res"].items():
    lam = [0.30, 0.35, 0.40, 0.45, 0.48, 0.50]
    a = r["zeta_A"]
    A = [a["mt_lam%.2f" % l] for l in lam]
    mk = "o-" if k == "600000" else "s--"
    ax.plot(lam, A, mk, lw=1.5, ms=4, label="zeta T=6e5" if k == "600000" else "zeta T=8e5")
    A2 = [a["mt_lam%.2f" % l] for l in lam]  # placeholder
ax.axhline(CMT, color="k", ls=":", lw=1.2, label="C_MT=1.3274993 (uncond. min)")
ax.axhline(1.125, color="crimson", ls="--", lw=1.0, label="7/8 threshold 1.125")
ax.set_xlabel("spectral support lambda (<=1/2 uncond. domain)")
ax.set_ylabel("pair constant A")
ax.set_title("(a) A vs lambda: min at lambda=0.5, A<C_MT")
ax.grid(True, ls=":", alpha=0.5)
ax.legend(fontsize=8, loc="upper left")
ax.set_xlim(0.28, 0.52)

# (b) ε 逼近族 + 单调收敛
ax = axs[1]
for k, r in d["res"].items():
    eps = [0.05, 0.10, 0.20]
    Az = [r["zeta_A"]["mt_eps%.2f" % e] for e in eps]
    Al = [r["L_A"]["mt_eps%.2f" % e] for e in eps]
    mk = "o-" if k == "600000" else "s--"
    ax.plot(eps, Az, mk, color="#1f4e79", lw=1.5, ms=5, label="zeta T=6e5" if k == "600000" else "zeta T=8e5")
    ax.plot(eps, Al, mk, color="#c00000", lw=1.5, ms=5, label="L T=6e5" if k == "600000" else "L T=8e5")
    amt = r["zeta_A"]["mt_lam0.50"]
    ax.axhline(amt, color="#1f4e79", ls=":", lw=1.0)
ax.axhline(CMT, color="k", ls=":", lw=1.2, label="C_MT")
ax.set_xlabel("eps (boundary smoothing width)")
ax.set_ylabel("pair constant A(eps)")
ax.set_title("(b) eps-family: monotone to optimal, all < C_MT")
ax.grid(True, ls=":", alpha=0.5)
ax.legend(fontsize=7, loc="upper left")
ax.set_xlim(0.04, 0.21)

# (c) 分解口径在线比例 vs 0.6725−10⁻²
ax = axs[2]
k6, k8 = d["res"]["600000"], d["res"]["800000"]
labels = ["T=6e5", "T=8e5"]
rat = [k6["ratio_dec_mt"], k8["ratio_dec_mt"]]
bar = ax.bar(labels, rat, width=0.5, color=["#1f4e79", "#2e75b6"])
ax.axhline(0.6725, color="k", ls=":", lw=1.2, label="0.6725 (2-C_MT)")
ax.axhline(0.6625, color="crimson", ls="--", lw=1.0, label="0.6725-10^-2 target")
for b, v in zip(bar, rat):
    ax.text(b.get_x() + b.get_width() / 2, v + 0.004, "%.4f" % v, ha="center", fontsize=9)
ax.set_ylim(0.6, 0.85)
ax.set_ylabel("union online-simple ratio (decomposed)")
ax.set_title("(c) 0.6725 strictified: margin 0.11")
ax.grid(True, ls=":", alpha=0.5, axis="y")
ax.legend(fontsize=8)

fig.tight_layout()
out = os.path.join(QRH, "xlii_s6_fig.png")
fig.savefig(out)
print("saved:", out)
