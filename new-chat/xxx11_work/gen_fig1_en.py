# -*- coding: utf-8 -*-
"""英文版图 1：配对常数 A 的核族×尺度扫描（audit6），全英文标签，与嵌入图同数据"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

kernels = ["fejer a=0.5", "sinc a=0.5", "fejer a=1.0", "gauss a=0.5", "MT optimal"]
A_zeta   = [1.0079, 1.0492, 1.0565, 1.1269, 1.1868]
A_L      = [1.0114, 1.0639, 1.0807, 1.1773, 1.2494]
A_union  = [1.2859, 1.4720, 1.6227, 1.8902, 2.0562]
C_MT = 1.3275
THR = 1.125

x = np.arange(len(kernels))
w = 0.26

fig, ax = plt.subplots(figsize=(9.2, 5.2), dpi=300)
b1 = ax.bar(x - w, A_zeta,  w, label=r"$\zeta$",      color="#4C72B0")
b2 = ax.bar(x,       A_L,     w, label=r"$L(\chi_5)$", color="#DD8452")
b3 = ax.bar(x + w, A_union, w, label=r"$\zeta\cup L$", color="#55A868")

ax.axhline(C_MT, color="#C44E52", linestyle="--", linewidth=1.4,
           label=r"$C_{MT}=1.3275$ (uncond. min.)")
ax.axhline(THR, color="#2CA02C", linestyle="--", linewidth=1.4,
           label=r"$7/8$ threshold $A=1.125$")

for bars, vals in ((b1, A_zeta), (b2, A_L), (b3, A_union)):
    for r, v in zip(bars, vals):
        ax.text(r.get_x() + r.get_width()/2, v + 0.02, f"{v:.4f}",
                ha="center", va="bottom", fontsize=7.2, rotation=90)

ax.set_xticks(x)
ax.set_xticklabels(kernels, fontsize=11)
ax.set_ylabel("Pair-correlation constant $A$", fontsize=12)
ax.set_ylim(0.9, 2.25)
ax.set_title(r"Pair-correlation constant $A$: kernel family $\times$ scale scan"
             r"  (audit6, $\delta=\log T/2\pi=2.1175$, histogram convention)",
             fontsize=12)
ax.legend(fontsize=10, loc="upper left")
ax.grid(axis="y", alpha=0.3)
fig.tight_layout()
out = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx11_work\fig1_A_scan_en.png"
fig.savefig(out, dpi=300)
print("SAVED", out)
