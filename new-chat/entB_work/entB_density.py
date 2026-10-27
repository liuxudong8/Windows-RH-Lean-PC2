# -*- coding: utf-8 -*-
"""入口 B 实验一：零密度定理深度-数量权衡曲线

N(σ,T) ≪ T^{3(1−σ)/(2−σ)} (log T)^5   [Ingham 型, σ∈[1/2,1)]
对 ζ 与 L(χ₅) 同型（L 函数有相同的零密度界），并集上界取 2×（保守）
目标带：N_off_simple ≤ 0.1018·N_K（λ₀=1.0 口径，攻防 XXXI）

输出：
- δ(=σ−1/2) 扫描下的 N_off_max(δ)/N_K（主幂口径 与 带 log^5 保守口径）
- δ* = 达到目标带 0.1018 的临界深度（二分求解）
- 与入口 A 的 N_off_max(δ)（ψ 均方反推）并排：两口径互补
"""
import json, math

T = 6e5
lam = math.log(T)                       # 13.30
pi2 = 2 * math.pi
N_K = 2149542.0                        # 数据实测（T=6e5 并集）
GATE = 0.1018                          # 目标带（λ₀=1.0）
GATE074 = 430.0 / N_K                  # λ₀=0.74 极严口径（相对）

def N_ing_abs(sigma, logf):
    """Ingham 型上界：T^{3(1−σ)/(2−σ)}·(logT)^logf；并集取 2×"""
    expo = 3.0 * (1.0 - sigma) / (2.0 - sigma)
    return 2.0 * T ** expo * (lam ** logf)

def N_K_main(T):
    # 攻防 XIX 主项：ζ: (T/2π)log(T/2π) − T/2π；L: (T/2π)[log(T/2π)+log5−1]
    a = T / pi2
    return a * (math.log(a) - 1.0) + a * (math.log(a) + math.log(5.0) - 1.0)

rows = []
deltas = [0.005, 0.01, 0.02, 0.03, 0.05, 0.06, 0.08, 0.1, 0.15, 0.2, 0.3, 0.4]
for d in deltas:
    s = 0.5 + d
    m0 = N_ing_abs(s, 0.0)                    # 主幂口径
    m5 = N_ing_abs(s, 5.0)                    # 保守（log^5）
    rows.append(dict(delta=d, sigma=s,
                     n_off_pow=m0, frac_pow=m0 / N_K,
                     n_off_log5=m5, frac_log5=m5 / N_K))

def solve_delta(logf, target_frac):
    lo, hi = 1e-4, 0.4
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if N_ing_abs(0.5 + mid, logf) / N_K > target_frac:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)

dst_pow = solve_delta(0.0, GATE)
dst_log5 = solve_delta(5.0, GATE)
dst_074 = solve_delta(0.0, GATE074)

out = dict(T=T, lam=lam, N_K=N_K, N_K_main=N_K_main(T),
           gate=GATE, gate074_abs=430.0,
           rows=rows,
           dst_pow=dst_pow, dst_log5=dst_log5, dst_074=dst_074,
           note="Ingham 型零密度 N(σ,T)≪T^{3(1−σ)/(2−σ)}(logT)^5，并集取 2×；δ* 为达到目标带的临界离线深度（深度≥δ* ⟹ 数量上界自动≤目标带）")
json.dump(out, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_density.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print("N_K(数据)=%d, N_K(主项)=%.0f, 目标带=%.0f (%.4f)" % (N_K, out["N_K_main"], GATE * N_K, GATE))
print("--- 零密度权衡（δ → N_off_max/N_K）---")
for r in rows:
    print("δ=%.3f  σ=%.3f  主幂 frac=%.4g   log^5 frac=%.4g" % (r["delta"], r["sigma"], r["frac_pow"], r["frac_log5"]))
print("δ*(主幂, 目标带 0.1018) = %.4f" % dst_pow)
print("δ*(log^5 保守, 目标带) = %.4f" % dst_log5)
print("δ*(主幂, λ₀=0.74 极严带 430 个) = %.4f" % dst_074)
print("saved entB_density.json")
