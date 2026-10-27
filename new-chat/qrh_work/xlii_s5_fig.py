# -*- coding: utf-8 -*-
"""S5 数值件 C 附图：跨族交叉配对常数三子图。
子图1：A_cross−1 vs a（对数坐标）——ζ×L、ζ×Poisson、ζ×Lshuf 对照 + 独立预测（修正因子2）
子图2：Δ_cross(a)=A_cross−A_ind（跨族微互斥剖面，双 T）
子图3：线性系数 C=A_cross−1/a 六档稳定性（双 T）
输出 xlii_s5_fig.png（dpi=200，供 S5 文档内嵌）。
"""
import numpy as np, json, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

D = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
cross = json.load(open(os.path.join(D, "xlii_s5_cross.json"), encoding="utf-8"))
ctl = json.load(open(os.path.join(D, "xlii_s5_ctl.json"), encoding="utf-8"))
A = cross["meta"]["A_grid"]

fig, axs = plt.subplots(1, 3, figsize=(13.2, 3.9))

# 子图1：线性标度 + 对照
r = cross["rows"][0]
c = ctl
ax = axs[0]
ax.plot(A, [r["A_cross"][str(a)] - 1 for a in A], "o-", color="#1f4e79", lw=1.6, ms=4, label="zeta x L (T=8e5)")
ax.plot(A, [r["A_cross_sym"][str(a)] - 1 for a in A], "s--", color="#2e75b6", lw=1.2, ms=3.5, label="zeta x L (L-centered)")
ax.plot(A, [c["A_cross_Poisson"][str(a)] - 1 for a in A], "^:", color="#7f7f7f", lw=1.2, ms=4, label="zeta x Poisson ctrl")
ax.plot(A, [c["A_cross_Lshuf"][str(a)] - 1 for a in A], "x:", color="#a5a5a5", lw=1.0, ms=4, label="zeta x L-shuffled")
ax.plot(A, [c["ind_win_Lratio"][str(a)] - 1 for a in A], "-", color="#c00000", lw=1.2, label="ind. pred. 2(rho_L/rho_zeta)int K^2")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("kernel width a (u=|Delta| rho_zeta)")
ax.set_ylabel("A_cross - 1")
ax.set_title("(a) cross-family pair constant: linear scaling vs ctrl")
ax.grid(True, which="both", ls=":", alpha=0.5)
ax.legend(fontsize=7.5, framealpha=0.9)
ax.set_xlim(4e-3, 0.5)

# 子图2：Δ_cross 剖面（双 T）
ax = axs[1]
for rr, mk, lb in [(cross["rows"][0], "o-", "T=8e5"), (cross["rows"][1], "s--", "T=6e5")]:
    dv = [rr["Delta_cross"][str(a)] for a in A]
    ax.plot(A, dv, mk, color="#1f4e79" if "8" in lb else "#c00000", lw=1.5, ms=4, label=lb)
ax.axhline(0, color="k", lw=0.8)
ax.set_xscale("log"); ax.set_yscale("symlog", linthresh=1e-3)
ax.set_xlabel("kernel width a")
ax.set_ylabel("Delta_cross = A_cross - A_ind")
ax.set_title("(b) cross-family mild repulsion vs independence")
ax.grid(True, which="both", ls=":", alpha=0.5)
ax.legend(fontsize=8)
ax.set_xlim(4e-3, 0.5)

# 子图3：线性系数稳定性
ax = axs[2]
for rr, mk, lb in [(cross["rows"][0], "o-", "T=8e5"), (cross["rows"][1], "s--", "T=6e5")]:
    cv = [rr["A_cross"][str(a)] / a for a in A]
    ax.plot(A, cv, mk, color="#1f4e79" if "8" in lb else "#c00000", lw=1.5, ms=4, label=lb)
ind_coef = 2.0 * (2.0263 / 1.7701) / 3.0
ax.axhline(ind_coef, color="k", ls=":", lw=1.2, label="ind. coef 2rho_L/3rho_zeta=%.4f" % ind_coef)
ax.set_xscale("log")
ax.set_ylim(0.6, 0.85)
ax.set_xlabel("kernel width a")
ax.set_ylabel("C = (A_cross-1)/a")
ax.set_title("(c) linear coefficient stability: C ~ 0.723")
ax.grid(True, which="both", ls=":", alpha=0.5)
ax.legend(fontsize=8)
ax.set_xlim(4e-3, 0.5)

fig.tight_layout()
out = os.path.join(D, "xlii_s5_fig.png")
fig.savefig(out, dpi=200)
print("saved:", out)
