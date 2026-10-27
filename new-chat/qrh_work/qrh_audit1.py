# -*- coding: utf-8 -*-
"""QRH 常数机制攻坚 · 数值定向 #1：三族零点统计的拟随机审计。
对象 K=ℚ(√5)，ζ_K=ζ·L(χ₅)，T=6e5 全零点（zeros_T6e5.npz）。
判定问题：拟随机前提（两族族内 GUE 排斥 + 跨族独立无排斥）在并集上的数值现实性。
审计指标（特征级对照，不做全分布拟合）：
  (i)   ζ 族内归一化最近间距：均值≈1、方差≈GUE 0.178、p(0+)≈0（排斥）、峰≈0.87；
  (ii)  L 族内同款——χ₅ 实字符 L 函数的单函数零点统计预测仍为 GUE；
  (iii) 跨族（ζ 零点 → 最近 L 零点）：方差≈1、p(0)≈1（泊松无排斥）——独立；
  (iv)  并集（全零点混合）最近间距：两族独立叠加的混合预测（λ 加权）。
归一化：ζ 密度 ρ_ζ(t)=(1/2π)log(t/2π)；L 密度 ρ_L(t)=(1/2π)[log(t/2π)+log5−1]（XIX 修正主项）。
输出 qrh_audit1.json：各族 n、均值/方差/峰位/p(0+)/小 s 指数、跨族泊松对照、并集混合对照。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\qrh_audit1.json"
T = 6.0e5

def rho_zeta(t):
    return np.log(t / (2.0 * np.pi)) / (2.0 * np.pi)

def rho_L(t):
    return (np.log(t / (2.0 * np.pi)) + np.log(5.0) - 1.0) / (2.0 * np.pi)

def stats_spacing(s, label, n_bin=40, s_max=4.0):
    s = np.asarray(s, dtype=float)
    s = s[np.isfinite(s)]
    mean = float(s.mean()) if len(s) else float("nan")
    var = float(s.var()) if len(s) else float("nan")
    # 峰位：直方图
    hist, edges = np.histogram(s, bins=n_bin, range=(0.0, s_max), density=True)
    peak = float(edges[np.argmax(hist)] + (edges[1] - edges[0]) / 2.0)
    # p(0+)：s<0.1 区间的密度均值（泊松 e^-s →≈0.95；GUE →≈0）
    small = s[s < 0.1]
    p0 = float(len(small) / len(s) / 0.1) if len(s) else float("nan")
    # 小 s 指数：拟合 log p ~ a log s（s<0.3）→ a≈1 泊松、≈2 GUE
    ss = s[s < 0.3]
    if len(ss) > 20:
        bc = np.bincount(np.clip((ss / 0.005).astype(int), 0, 59), minlength=60)[0:60]
        xb = (np.arange(60) + 0.5) * 0.005
        m = bc > 0
        a = float(np.polyfit(np.log(xb[m]), np.log(bc[m]), 1)[0])
    else:
        a = float("nan")
    rec = {"label": label, "n": int(len(s)), "mean": mean, "var": var,
           "peak": peak, "p0plus": p0, "small_s_exp": a}
    print("%-24s n=%7d  mean=%.4f  var=%.4f  peak=%.3f  p(0+)=%.3f  s-exp=%.2f"
          % (label, rec["n"], mean, var, peak, p0, a))
    return rec

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[z <= T]; l = l[l <= T]
    nz, nl = len(z), len(l)
    print("nz=%d nl=%d N_K=%d" % (nz, nl, nz + nl))
    res = {}

    # ---- (i) ζ 族内归一化最近间距 ----
    r = np.minimum(np.diff(z), np.concatenate([[np.inf], np.diff(z)[1:]]))
    r = np.concatenate([r, [np.inf]])
    # 局部密度：用前/后邻间距中点的密度平均（稳健）
    mid = (z[:-1] + z[1:]) / 2.0
    s_z = r[:-1] * rho_zeta(mid)
    s_z = s_z[np.isfinite(s_z)]
    res["zeta_internal"] = stats_spacing(s_z, "zeta_internal")

    # ---- (ii) L 族内 ----
    rL = np.minimum(np.diff(l), np.concatenate([[np.inf], np.diff(l)[1:]]))
    rL = np.concatenate([rL, [np.inf]])
    midL = (l[:-1] + l[1:]) / 2.0
    s_l = rL[:-1] * rho_L(midL)
    s_l = s_l[np.isfinite(s_l)]
    res["L_internal"] = stats_spacing(s_l, "L_internal")

    # ---- (iii) 跨族：ζ 零点 → 最近 L 零点（用 L 局部密度归一化） ----
    idx = np.searchsorted(l, z, side="right")
    idx = np.clip(idx, 1, len(l) - 1)
    dL = np.minimum(np.abs(l[idx] - z), np.abs(l[idx - 1] - z))
    s_cross = dL * rho_L(z)
    s_cross = s_cross[np.isfinite(s_cross)]
    res["cross_zeta_to_L"] = stats_spacing(s_cross, "cross_zeta_to_L")

    # 反向：L 零点 → 最近 ζ 零点（ζ 局部密度归一化）
    idxz = np.searchsorted(z, l, side="right")
    idxz = np.clip(idxz, 1, len(z) - 1)
    dZ = np.minimum(np.abs(z[idxz] - l), np.abs(z[idxz - 1] - l))
    s_cross2 = dZ * rho_zeta(l)
    s_cross2 = s_cross2[np.isfinite(s_cross2)]
    res["cross_L_to_zeta"] = stats_spacing(s_cross2, "cross_L_to_zeta")

    # ---- (iv) 并集混合最近间距（各用各族的局部密度归一化） ----
    zz = np.stack([z, np.full(nz, 0.0, dtype=float)], axis=1)
    ll = np.stack([l, np.full(nl, 1.0, dtype=float)], axis=1)
    allz = np.concatenate([zz, ll])
    allz = allz[np.argsort(allz[:, 0])]
    tt = allz[:, 0]; kind = allz[:, 1]
    dt_int = np.diff(tt)
    rho_mid = np.where(kind[:-1] == 0, rho_zeta((tt[:-1] + tt[1:]) / 2.0),
                       rho_L((tt[:-1] + tt[1:]) / 2.0))
    rho_after = np.where(kind[1:] == 0, rho_zeta((tt[:-1] + tt[1:]) / 2.0),
                         rho_L((tt[:-1] + tt[1:]) / 2.0))
    # 并集最近间距（最小邻间距，含跨族与族内），归一化用间距两端的密度均值
    sp = np.minimum(dt_int, np.concatenate([[np.inf], dt_int[1:]]))
    sp = np.concatenate([sp, [np.inf]])
    midall = (tt[:-1] + tt[1:]) / 2.0
    rho_pair = (rho_zeta(midall) + rho_L(midall)) / 2.0  # 混合密度近似
    s_K = sp[:-1] * rho_pair
    s_K = s_K[np.isfinite(s_K)]
    res["union_mixed"] = stats_spacing(s_K, "union_mixed")

    # ---- 理论对照（特征值） ----
    ref = {
        "GUE": {"var": 0.178, "p0plus": 0.0, "small_s_exp": 2.0, "peak": 0.87},
        "poisson": {"var": 1.0, "p0plus": 1.0, "small_s_exp": 1.0, "peak": 0.0},
        "GOE_note": "实字符 L 函数单函数零点统计预测仍为 GUE（对称型是族统计，单 L 函数无对称型）",
        "union_mixed_pred": "两族独立叠加：λ=N_z/(N_z+N_l)≈0.465 加权的 GUE/泊松混合（跨族间距泊松、族内 GUE）",
        "data": {"T": T, "nz": nz, "nl": nl, "N_K": nz + nl,
                 "lambda_zeta": float(nz / (nz + nl))}
    }
    res["reference"] = ref
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"results": res, "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
