# -*- coding: utf-8 -*-
"""数值件 F 图：超支撑素数项量级与二阶校正形态（双子图，d1 文档嵌入用）。"""
import json, os, math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei", "DejaVu Sans"]
plt.rcParams["axes.unicode_minus"] = False

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
with open(os.path.join(QRH, "xlii_s7f_supersupport.json"), encoding="utf-8") as f:
    res = json.load(f)

s = res["samples"]
Xs = np.array([d["X"] for d in s], dtype=float)
r_NL = np.array([d["|S_a|/N_L"] for d in s], dtype=float)
r_sq = np.array([d["|S_a|/(√X·logX)"] for d in s], dtype=float)
r_raw = np.array([d["|S_raw|/(√X·logX)"] for d in s], dtype=float)

fe = res["form_exp"]
a_scan = np.array([d["a"] for d in fe["a_scan"] if d["a"] > 0], dtype=float)
ad = np.array([d["a_delta"] for d in fe["a_scan"] if d["a"] > 0], dtype=float)
dS = np.array([abs(d["dS"]) for d in fe["a_scan"] if d["a"] > 0], dtype=float)

fig, axes = plt.subplots(1, 2, figsize=(11.5, 4.6))

# 左：超支撑素数项相对 N_L 衰减
ax = axes[0]
ax.loglog(Xs, r_NL, "o-", color="#C0392B", lw=1.6, ms=5, label="|S_a|/N_L (超支撑 λ=logT)")
ax.loglog(Xs, r_sq, "s--", color="#2471A3", lw=1.3, ms=4, label="|S_a|/(√X·logX)")
ax.loglog(Xs, Xs ** -0.5, "-", color="#7F8C8D", lw=1.1, label="X^{-1/2}（理论下界参考）")
ax.loglog(Xs, Xs ** -2.0, ":", color="#7F8C8D", lw=1.1, label="X^{-2}（实测衰减参考）")
ax.set_xlabel("X（素数上限，T≈X 量级）")
ax.set_ylabel("比值（对数轴）")
ax.set_title("超支撑素数项：相对零点数 N_L 可忽略性")
ax.legend(fontsize=8, loc="lower left")
ax.grid(True, which="both", alpha=0.3)

# 右：二阶校正形态 dS ~ (aδ)²
ax = axes[1]
ax.loglog(ad, dS, "o-", color="#C0392B", lw=1.6, ms=5, label="|δS|（核加权-常数核）")
ax.loglog(ad, 0.5 * abs(fe["Kpp0_numeric"]) * ad ** 2 * abs(fe["T2"]),
          "--", color="#2471A3", lw=1.3, label="|K''(0)|·(aδ)²·|T2| 的一半（二阶预测）")
ax.set_xlabel("aδ（核宽×频域步长，对数轴）")
ax.set_ylabel("校正量（对数轴）")
ax.set_title("偶核形态：一阶校正为零，二阶主导")
ax.legend(fontsize=8, loc="upper left")
ax.grid(True, which="both", alpha=0.3)
ax.text(0.03, 0.03, "K''(0) ≈ -3.06\nratio=1.000 @ aδ≤3e-3",
        transform=ax.transAxes, fontsize=8, va="bottom", ha="left",
        bbox=dict(boxstyle="round", fc="white", alpha=0.85))

plt.tight_layout()
out = os.path.join(QRH, "xlii_s7f_fig.png")
plt.savefig(out, dpi=200)
print("saved", out)
