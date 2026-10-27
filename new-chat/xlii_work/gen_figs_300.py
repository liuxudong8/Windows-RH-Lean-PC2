# -*- coding: utf-8 -*-
"""XLII 文档嵌入图：300dpi 重渲染（ASCII 标签），输出 xlii_work。"""
import json, numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xlii_work"
plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei"]
plt.rcParams["axes.unicode_minus"] = False

v3 = json.load(open(QRH + r"\xlii_s0_v3.json", encoding="utf-8"))
gue = json.load(open(QRH + r"\xlii_s0_gue_sim.json", encoding="utf-8"))
AGRID = [0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]
lam = [np.pi / a for a in AGRID]
Az = [v3["A_zeta_fine"][str(a)] for a in AGRID]
Al = [v3["A_L_fine"][str(a)] for a in AGRID]
G2 = [v3["A_GUE2"][str(a)] for a in AGRID]
P2 = [v3["A_Poisson2"][str(a)] for a in AGRID]
AG = [0.5, 1.0, 2.0, 4.0, 8.0]
Asim = [gue["A"][str(a)]["mean"] for a in AG]

# fig1
fig, ax = plt.subplots(figsize=(10.5, 6.2))
ax.plot(lam, P2, "--", color="gray", lw=1.0, label="Poisson baseline (ordered pairs)")
ax.plot(lam, G2, "-", color="tab:blue", lw=1.6, label="GUE prediction (two-sided)")
ax.plot(lam, Az, "o-", color="k", ms=5, lw=1.1, label="zeta observed (local norm)")
ax.plot(lam, Al, "s-", color="tab:red", ms=5, lw=1.1, label="L(chi5) observed (density cal.)")
ax.axhline(1.125, color="tab:green", ls=":", lw=1.4, label="7/8 threshold A<=1.125")
ax.axhline(1.3275, color="tab:orange", ls="-.", lw=1.2, label="C_MT=1.3275 (unconditional)")
ax.annotate("XLI optimal kernel fejer_a0.5\n(lambda_eff=6.28)", xy=(6.28, 1.0149),
            xytext=(16, 1.45), arrowprops=dict(arrowstyle="->", lw=1.0), fontsize=9)
ax.annotate("narrow end monotone to 1:\na=0.5->0.1, A-1: 0.015->1.3e-4",
            xy=(31.4, 1.00013), xytext=(2.0, 1.02), arrowprops=dict(arrowstyle="->", lw=1.0), fontsize=9)
ax.set_xscale("log")
ax.set_xlim(0.35, 40); ax.set_ylim(0.99, 6.6)
ax.set_xlabel("spectral support lambda_eff = pi/a (log)"); ax.set_ylabel("pair constant A")
ax.set_title("XLII S0: A(lambda) full curve vs two-sided GUE/Poisson (T=6e5, local normalization)")
ax.legend(fontsize=9, loc="upper left")
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(OUT + r"\xlii_s0_fig1_300.png", dpi=300)
plt.close(fig)

# fig2
fig, ax = plt.subplots(figsize=(10.5, 6.0))
ax.loglog(AG, [x - 1.0 for x in Asim], "^-", color="tab:purple", ms=7, lw=1.2,
          label="GUE simulation (N=4000 x12, cal.)")
ax.loglog(lam, [x - 1.0 for x in G2], "-", color="tab:blue", lw=1.6, label="GUE2 theory A-1")
ax.loglog(lam, [x - 1.0 for x in Az], "o-", color="k", ms=5, lw=1.1, label="zeta obs A-1")
ax.loglog(lam, [x - 1.0 for x in Al], "s-", color="tab:red", ms=5, lw=1.1, label="L obs A-1")
ax.loglog([0.1, 0.5], [1e-4, 1e-4], ":", color="green", lw=1.0)
ax.annotate("a=0.1: A-1 ~ 1.3e-4", xy=(0.1, 1.3e-4), xytext=(0.13, 3e-4), fontsize=9)
ax.set_xlabel("kernel width a (lambda_eff = pi/a)"); ax.set_ylabel("A-1 (log)")
ax.set_title("S0: A-1 convergence (monotone to 1 at narrow end; observed slightly below GUE - super-GUE repulsion)")
ax.legend(fontsize=9); ax.grid(alpha=0.3, which="both")
fig.tight_layout()
fig.savefig(OUT + r"\xlii_s0_fig2_300.png", dpi=300)
plt.close(fig)
print("300dpi figs saved to", OUT)
