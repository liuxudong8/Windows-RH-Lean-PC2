# -*- coding: utf-8 -*-
"""S4 数值件 B 配图：窄核标度 + 残差结构 ε(a) + λ 路径与噪声带。"""
import json, math, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei"]
plt.rcParams["axes.unicode_minus"] = False

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
res = json.load(open(os.path.join(QRH, "xlii_s4b.json"), encoding="utf-8"))
FIG = os.path.join(QRH, "xlii_s4b_fig.png")
AV = np.array(res["meta"]["A_grid"])
fig, axes = plt.subplots(1, 3, figsize=(18, 6))
colors = {"zeta": "#1f77b4", "L": "#d62728"}
mks = {"zeta": "o", "L": "s"}

# 左：log-log 标度（T=8e5）
ax = axes[0]
r8 = res["rows"][0]
G = np.array([r8["GUE2"][str(a)] - 1.0 for a in AV])
ax.plot(AV, G, "k-", lw=2, label="GUE2-1")
for fam in ("zeta", "L"):
    A1 = np.array([r8["A_minus_1"][fam][str(a)] for a in AV])
    D = np.array([abs(r8["Delta"][fam][str(a)]) for a in AV])
    ax.plot(AV, A1, color=colors[fam], marker=mks[fam], ls="--", label=fam+" A-1")
    ax.plot(AV, D, color=colors[fam], marker=mks[fam], ls=":", label=fam+" |Delta|")
ax.plot(AV, 0.16 * AV ** 3, color="gray", ls=":", lw=1, label="0.16 a^3 (fit)")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("a"); ax.set_title("T=8e5 窄核标度 (log-log)")
ax.grid(alpha=0.3, which="both"); ax.legend(fontsize=8)

# 中：残差比 ε=A-1/GUE2-1
ax = axes[1]
for r_ in res["rows"]:
    G = np.array([r_["GUE2"][str(a)] - 1.0 for a in AV])
    for fam in ("zeta", "L"):
        A1 = np.array([r_["A_minus_1"][fam][str(a)] for a in AV])
        eps = A1 / G
        ax.plot(AV, eps, color=colors[fam], marker=mks[fam],
                label="%s T=%.0e" % (fam, r_["T"]))
ax.axhline(1.0, color="gray", ls="--", lw=0.8)
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("a"); ax.set_title("epsilon(a)=A-1/(GUE2-1) 残差剖面")
ax.grid(alpha=0.3, which="both"); ax.legend(fontsize=8)

# 右：λ 路径与噪声带
ax = axes[2]
lp = res["lambda_path"]
ax.plot([p["T"] for p in lp], [p["lambda_15_7"] for p in lp], "k-o", label="lambda(T)=(logT)^{-15/7}")
ax.axhspan(0.0003, 0.003, color="gray", alpha=0.15, label="a<0.005 噪声带")
ax.axhline(0.1, color="blue", ls="--", lw=0.8, label="a=0.1 (S2(ii) 最小核)")
ax.axhline(0.005, color="red", ls="--", lw=0.8, label="a=0.005 (S4 实测最小)")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("T"); ax.set_title("lambda 路径落点 vs 实测核区间")
ax.grid(alpha=0.3, which="both"); ax.legend(fontsize=8)

fig.suptitle("S4 数值件 B: 窄核实测标度与残差结构 (T=8e5/6e5, half=0.5, binw=0.0005)", fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.93])
fig.savefig(FIG, dpi=150)
print("fig:", FIG)
