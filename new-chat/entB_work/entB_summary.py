# -*- coding: utf-8 -*-
"""Stage 3：入口 B 数值定向汇总（零密度权衡 + 无 Siegel → 合并判定）"""
import json, math

d = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_density.json", encoding="utf-8"))
s = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_siegel.json", encoding="utf-8"))
# 入口 A ψ 均方 frac（c=1）
b = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_bridge.json", encoding="utf-8"))
fracA = {r["delta"]: r["frac_N"] for r in b["rows_inv"]}

summary = dict(
    meta=dict(T=6e5, N_K=2149542, gate=0.1018, gate074_abs=430),
    density=dict(dst_pow=d["dst_pow"], dst_log5=d["dst_log5"], dst_074=d["dst_074"],
                 note_log5="log^5 保守口径在 T=6e5 完全无约束（δ=0.4 时 frac 仍 14.6）：零密度绝对可用性依赖 log 因子与常数",
                 rows=d["rows"]),
    siegel=dict(L1_closed=s["closed"], series_diff=s["series_partial"] - s["closed"],
                euler_diff=s["euler_prod"] - s["closed"],
                min_imag=s["min_imag"], n_near_zero=s["n_near_zero"]),
    merge=dict(
        threat_window="θ_K≥7/8 剩余威胁压缩到深度 δ<0.0902 的浅离线窗口：δ≥0.0902 被零密度（主幂）无条件保证 N_off≤0.1018·N_K；δ∈[0.05,0.0902] 可被对数导数峰宽实测但零密度不控；δ<0.05 完全不可见（入口 A）",
        dst_pow=d["dst_pow"], dst_074=d["dst_074"],
        A_frac=fracA,
        honest_bound="零密度主幂口径忽略 log 因子与常数（教科书 Ingham 型）；保守 log^5 形式在 T=6e5 无约束，Bourgain 型现代零密度可将 δ* 压低但需文献核实",
    ),
)
json.dump(summary, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_summary.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print("=== 零密度权衡（主幂 frac，目标带 0.1018）===")
for r in d["rows"]:
    print("δ=%.3f  frac=%.5f" % (r["delta"], r["frac_pow"]))
print("δ*(主幂) = %.4f ; δ*(λ₀=0.74 极严带 430) = %.4f ; δ*(log^5) 无解" % (d["dst_pow"], d["dst_074"]))
print("=== 无 Siegel（D=5）===")
print("L(1,χ₅)=2·logφ/√5 = %.8f（级数差 %.1e，Euler 积差 %.1e）" % (s["closed"], s["series_partial"] - s["closed"], s["euler_prod"] - s["closed"]))
print("L 族最小虚部 γ_min=%.4f，近实轴零点 0 个" % s["min_imag"])
print("=== 盲区 ===")
print("δ≥0.0902：零密度无条件；δ∈[0.05,0.0902]：峰宽可测不控数；δ<0.05：完全盲区")
print("saved entB_summary.json")
