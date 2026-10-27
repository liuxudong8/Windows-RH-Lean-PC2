# -*- coding: utf-8 -*-
"""生成图 1：配对常数 A 的核族 × 尺度扫描（audit6 数据，嵌入攻防 XLI）"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei"]
plt.rcParams["axes.unicode_minus"] = False

kernels = ["fejer_a0.5", "sinc_a0.5", "fejer_a1.0", "gauss_a0.5", "MT 最优核"]
A_zeta = [1.0079, 1.0492, 1.0565, 1.1269, 1.1868]
A_L = [1.0114, 1.0639, 1.0807, 1.1773, 1.2494]
A_union = [1.2859, 1.4720, 1.6227, 1.8902, 2.0562]
C_MT = 1.3275
TH = 1.125

x = np.arange(len(kernels))
w = 0.26
fig, ax = plt.subplots(figsize=(9.2, 5.2), dpi=300)
b1 = ax.bar(x - w, A_zeta, w, label="ζ 族 A_ζ", color="#4C72B0")
b2 = ax.bar(x, A_L, w, label="L(χ₅) 族 A_L", color="#DD8452")
b3 = ax.bar(x + w, A_union, w, label="并集 A_union", color="#8172B3")

ax.axhline(C_MT, color="red", ls="--", lw=1.4)
ax.text(4.32, C_MT + 0.014, "C_MT=1.3275（无条件极小）", color="red", ha="right", fontsize=9)
ax.axhline(TH, color="green", ls="-.", lw=1.4)
ax.text(4.32, TH + 0.014, "7/8 门槛 A≤1.125", color="green", ha="right", fontsize=9)

for bars in (b1, b2, b3):
    for rect in bars:
        h = rect.get_height()
        ax.annotate("{:.4f}".format(h), (rect.get_x() + rect.get_width() / 2, h),
                    textcoords="offset points", xytext=(0, 3), ha="center", fontsize=8)

ax.set_xticks(x)
ax.set_xticklabels(kernels, fontsize=10)
ax.set_ylabel("配对常数 A = ΣK²/Σ1", fontsize=11)
ax.set_ylim(0.95, 2.25)
ax.legend(loc="upper left", fontsize=10, frameon=True)
ax.grid(axis="y", ls=":", alpha=0.5)
ax.set_title("配对常数 A 的核族 × 尺度扫描（audit6，δ=2.1175）", fontsize=12)
fig.tight_layout()
fig.savefig(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx11_work\fig1_A_scan.png")
print("FIG SAVED")
