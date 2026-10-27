# -*- coding: utf-8 -*-
"""盲区理论门槛核实数值件：Ingham / Guth-Maynard / 密度假设 三条零密度路径在 δ 网格上的 frac 与 δ*。
口径与攻防 XXXIII B1 完全一致：frac(δ)=2·T^{κ(σ)}/N_K（并集 2×、主幂）；δ* 为 frac=gate 的临界深度。
"""
import json, math

T = 6.0e5
lnT = math.log(T)
N_K = 2149542.0
gate = 0.1018

def kappa_ingham(sigma):
    return 3.0 * (1.0 - sigma) / (2.0 - sigma)

def kappa_gm(sigma):
    # Guth-Maynard 2024：N(σ,T)≪T^{30(1−σ)/13+o(1)}（σ∈[1/2,3/4] 统一形式；σ≤0.7 时劣于 Ingham，取 min）
    return 30.0 * (1.0 - sigma) / 13.0

def kappa_dh(sigma):
    # 密度假设：N(σ,T)≪T^{2(1−σ)+ε}
    return 2.0 * (1.0 - sigma)

def frac(kappa):
    return 2.0 * math.exp(kappa * lnT) / N_K

def kappa_at_gate():
    # frac=gate 对应的指数：exp(κ·lnT)·2/N_K=gate ⟹ κ=ln(gate·N_K/2)/lnT
    return math.log(gate * N_K / 2.0) / lnT

deltas = [0.005, 0.01, 0.02, 0.03, 0.05, 0.06, 0.08, 0.09, 0.1]
paths = [("Ingham 1940  3(1−σ)/(2−σ)", kappa_ingham),
         ("Guth-Maynard 2024  30(1−σ)/13", kappa_gm),
         ("密度假设  2(1−σ)", kappa_dh)]

rows = []
for d in deltas:
    s = 0.5 + d
    r = {"delta": d, "sigma": s}
    for name, f in paths:
        k = f(s)
        r[name] = {"kappa": k, "frac": frac(k), "below_gate": frac(k) < gate}
    rows.append(r)

def bisect_dstar(f, lo=0.0, hi=0.5, tol=1e-9):
    # 解 frac(f(0.5+d))=gate
    def g(d):
        return frac(f(0.5 + d)) - gate
    if g(lo) <= 0:
        return lo
    if g(hi) >= 0:
        return None
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if g(mid) > 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)

kg = kappa_at_gate()
out = {
    "T": T, "lnT": lnT, "N_K": N_K, "gate": gate,
    "kappa_gate": kg,          # frac=0.1018 的指数门槛
    "delta_star_ingham": bisect_dstar(kappa_ingham),
    "delta_star_gm": bisect_dstar(kappa_gm),
    "delta_star_dh": bisect_dstar(kappa_dh),
    "rows": rows,
    "note": "frac=2·T^{κ}/N_K（主幂、并集 2×，与 entB_density 一致）。κ_gate=0.8723：盲区 δ<0.05 无条件闭合需 σ=0.55 处指数≤0.8723。",
}
print(json.dumps(out, ensure_ascii=False, indent=1))
with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entD_work\entD_zero_density_lit.json", "w", encoding="utf-8") as fp:
    json.dump(out, fp, ensure_ascii=False, indent=1)
print("SAVED entD_work/entD_zero_density_lit.json")
