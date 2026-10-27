# -*- coding: utf-8 -*-
"""S4 预演补分析：小 a 局部指数（GUE2−1 与 Δ 的分段幂律），验证 kg→3 理论预期，
并给出 A(λ;T)−1 主导项判定：A−1 = c1·λ^kg − c2(T)·λ^q，谁主导、符号、跨 T 稳定性。"""
import json, math, os
import numpy as np

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
res = json.load(open(os.path.join(QRH, "xlii_s2ii.json"), encoding="utf-8"))
gue2 = res["meta"]["gue2"]
rows = res["rows"]
gkeys = sorted(gue2.keys(), key=lambda s: float(s))
AV = np.array([float(a) for a in gkeys])
print("a grid:", AV)
g1 = np.array([gue2[a] - 1.0 for a in gkeys])
# 分段局部指数
print("GUE2-1 values:", ["%.6e" % v for v in g1])
for i in range(len(AV) - 1):
    k = math.log(g1[i + 1] / g1[i]) / math.log(AV[i + 1] / AV[i])
    print("  local power [%.3g, %.3g]: %.4f" % (AV[i], AV[i + 1], k))
# 全六点
la, lg = np.log(AV), np.log(g1)
kg, bg = np.polyfit(la, lg, 1)
print("full fit kg=%.4f exp(bg)=%.6e" % (kg, math.exp(bg)))
# 理论预期（换元 u=ax）：GUE2-1 = 2a∫(1-sinc²(πax))sinc⁴(πx)dx → a→0: (2π²/3)a³∫x²sinc⁴(πx)dx
print("theory small-a exponent: 3 (leading term 2a∫(πax)²/3·sinc⁴(πx)dx)")

# Δ 的局部指数（末档 T=8e5，最可信；双族）
A = rows[-1]["A"]
T = rows[-1]["T"]
for fam in ("zeta", "L"):
    D = np.array([A[fam][a] - gue2[a] for a in gkeys])
    print("\nfam=%s T=%.0e Δ values:" % (fam, T), ["%+.6e" % v for v in D])
    for i in range(len(AV) - 1):
        if D[i] * D[i + 1] > 0:
            k = math.log(abs(D[i + 1] / D[i])) / math.log(AV[i + 1] / AV[i])
            print("  local power [%.3g, %.3g]: %.4f" % (AV[i], AV[i + 1], k))

# 主导项判定：A-1 符号与量级（λ 走 (logT)^{-2.14} 路径时落入的 a 区间）
print("\nλ(T)=(logT)^{-15/7} 落入区间:")
for Tt in (1e4, 1e5, 8e5):
    lmb = 1.0 / (math.log(Tt) ** (15.0 / 7.0))
    print("  T=%.0e λ=%.4e  → 介于 a=%s 与 %s 之间" % (Tt, lmb, "0.0", "0.1" if lmb < 0.1 else "0.1+"))
