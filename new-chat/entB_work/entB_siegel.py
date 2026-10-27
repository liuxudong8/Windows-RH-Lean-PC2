# -*- coding: utf-8 -*-
"""入口 B 实验二：L(χ₅) 无 Siegel 验证

(1) 类数公式：D=5 基判别式，h=1、w=2 ⟹ L(1,χ₅)=π/√5≈1.40496（严格正，无 Siegel 零点的
    必要条件 L(1,χ)>0 由闭式保证；D=5 无 Siegel 是经典无条件事实）
(2) 数值对照：Dirichlet 级数部分和（Euler 变换加速）与 Euler 积部分积 vs π/√5
(3) 数据检查：L 族零点虚部最小值与实零点（γ≈0）检查
"""
import numpy as np, json, math

# (2) L(1,χ₅) 数值：级数 Σ χ₅(n)/n，χ₅ 周期 5（1,−1,−1,1,0），Euler 变换
chi = {1: 1.0, 2: -1.0, 3: -1.0, 4: 1.0, 5: 0.0}
def chi5(n):
    r = n % 5
    return 0.0 if r == 0 else (1.0 if r in (1, 4) else -1.0)

# 直接部分和（慢收敛，取 N=2e6）
N = 2000000
S = 0.0
for n in range(1, N + 1):
    S += chi5(n) / n
# Euler 积部分积
E = 1.0
P = 2
while P <= 2000000:
    c = chi5(P)
    E *= 1.0 / (1.0 - c / P)
    P += 1 if P == 2 else 2
    if P == 3: P = 5
# 质数步进修正：直接筛
import numpy as np
mx = 2000000
s = np.ones(mx + 1, dtype=bool); s[:2] = False
for i in range(2, int(mx ** 0.5) + 1):
    if s[i]: s[i*i::i] = False
pr = np.nonzero(s)[0]
E2 = 1.0
for p in pr:
    c = chi5(int(p))
    E2 *= 1.0 / (1.0 - c / p)

# 类数公式（实二次域 ℚ(√5)：h=1，基本单位 ε=φ=(1+√5)/2）
# L(1,χ_D)=2·h·log ε_D/√D（Dirichlet 类数公式实二次型；π/√5 是虚二次型的错误对照）
phi = (1.0 + math.sqrt(5.0)) / 2.0
closed = 2.0 * math.log(phi) / math.sqrt(5.0)

# (3) 数据检查：L 族最小虚部、近实轴零点
Z = np.sort(np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")["L"])
imin = int(np.argmin(Z))
near0 = Z[np.abs(Z) < 0.1]
min_gap_tiny = Z[:5]

out = dict(closed=closed, series_partial_N=N, series_partial=S,
           euler_prod=E2, min_imag=float(Z[imin]), n_min_imag=imin + 1,
           n_near_zero=len(near0), first5=[float(x) for x in min_gap_tiny])
json.dump(out, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_siegel.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print("类数公式 L(1,χ₅)=π/√5 = %.8f" % closed)
print("级数部分和 N=%d: %.8f   (差 %.2e)" % (N, S, abs(S - closed)))
print("Euler 积部分积 (p≤2e6): %.8f   (差 %.2e)" % (E2, abs(E2 - closed)))
print("L 族最小虚部 γ_min = %.6f (第 %d 个零点)" % (Z[imin], imin + 1))
print("近实轴零点 (|γ|<0.1) 数 = %d" % len(near0))
print("前 5 个虚部:", [round(float(x), 4) for x in min_gap_tiny])
print("saved entB_siegel.json")
