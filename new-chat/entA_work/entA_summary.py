# -*- coding: utf-8 -*-
"""Stage 3：入口 A 数值定向汇总判定（三个实验 → 结论）"""
import json, math

b = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_bridge.json", encoding="utf-8"))
ld = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_ld.json", encoding="utf-8"))
ep = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_eps.json", encoding="utf-8"))

N_K = b["meta"]["N_K"]
N_Z, N_L = b["meta"]["N_Z"], b["meta"]["N_L"]
lam = b["meta"]["lam"]
C_R = b["M_on_stats"]["C_R"]

# 实验1：ψ 均方口径 N_off_max(δ)/N_K（c=1, c=0.5）
rows1 = []
for r in b["rows_inv"]:
    rows1.append(dict(delta=r["delta"], Kmax_c1=r["Kmax_c1"], Kmax_c05=r["Kmax_c05"],
                      frac_c1=r["Kmax_c1"] / N_K, frac_c05=r["Kmax_c05"] / N_K))
# 实验2：对数导数单峰 SNR_h=1/(δ·rms_bg)，背景积分（解析）
rms_bg = ld["meta"]["rms_bg"]
int_bg = ld["meta"]["int_bg"]
rows2 = []
for r in ld["rows"]:
    if r["K"] == 430:   # 每 δ 取 K=430 行代表
        rows2.append(dict(delta=r["delta"], snr_h=r["snr_h"], area_pk=r["area_pk"],
                          snr_int=r["snr_int"]))
# 实验3：ε 正则化背景（σ>1/2 收敛）
rows3 = [dict(eps=float(k), bg_rms=v["bg_rms"], bg_pow=v["bg_pow"], peak_h=1.0/float(k),
              snr=v["supF"] / v["bg_rms"]) for k, v in ep["res"].items()]

GATE = dict(lam10_frac=0.1018, lam10_abs=0.1018 * N_K, lam074_abs=430.0)

summary = dict(
    meta=dict(N_K=N_K, N_Z=N_Z, N_L=N_L, lam=lam, C_R=C_R, T=6e5),
    exp1_psi_ms=rows1,
    exp2_ld_snr=rows2,
    exp3_eps_reg=rows3,
    gates=GATE,
    verdict=dict(
        psi_ms="空桥：E|B|²≈K·wbar（wbar~1e-11~1e-9），K=21.9万时相对效应0.66%，N_off_max(c=1)>>N_K 全部无约束",
        pair_S_sigmaK2="对σ盲：定理3.1′、S(t)、Levinson ΣK² 均为纯虚部差口径，离线零点一阶不可见",
        ld_peak="机制存在（每零点峰面积π，与δ无关），但背景rms=13.45（X=1e6）限单峰分辨δ≥~0.074；ε正则化后背景收敛但rms 3~8，SNR仅1.7~2.5",
        conclusion="入口A（显式公式余项桥）在T=6e5对浅深度（δ≤0.05）离线零点无约束力；离线零点唯一干净签名在σ方向（密度剖面=入口B）；入口A仅在与深度界合并（若δ_max已知）时有用",
    ),
)
json.dump(summary, open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_summary.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
# 打印核心判定表
print("=== 实验1 ψ均方口径 N_off_max/N_K (c=1) ===")
for r in rows1:
    print("δ=%.3f  frac=%.1f·N_K" % (r["delta"], r["frac_c1"]))
print("=== 实验2 对数导数单峰 SNR_h ===")
for r in rows2:
    print("δ=%.3f  SNR_h=%.3f" % (r["delta"], r["snr_h"]))
print("=== 实验3 ε正则化背景 ===")
for r in rows3:
    print("ε=%.2f  bg_rms=%.3f  SNR=%.2f" % (r["eps"], r["bg_rms"], r["snr"]))
print("目标带: λ₀=1.0 → %.0f（%.4f·N_K）; λ₀=0.74 → %.0f" % (GATE["lam10_abs"], GATE["lam10_frac"], GATE["lam074_abs"]))
print("saved entA_summary.json")
