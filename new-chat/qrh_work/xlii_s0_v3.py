# -*- coding: utf-8 -*-
"""攻防 XLII · S0 数值定向 v3（终版口径）：
- 有序全对（i≠j，两侧）约定：Poisson A=1+2a/3；GUE A=1+2∫₀^∞(1−sinc²(πu))·sinc⁴(πu/a)du
  （v1/v2 的"超 Poisson 上偏"系单侧对照缺因子 2 的伪影，已定位）。
- 局部归一化 u=|Δ|·ρ(t_mid)（ζ 用 ρζ，L 用校准 ρ_L_adj）。
- L 密度校准：ρ_L=(1/2π)[log(t/2π)+log5−1] 的 −1 项致 nn_mean≈0.92；检验 ρ_L+1/(2π)（去−1）。
- 全局 δ 口径（audit6 复现）对照，报告口径差对 XLI 数值的影响。
输出 xlii_s0_v3.json + fig1（A(λ) vs 双侧 GUE/Poisson）+ fig2（A−1 log-log + 段间漂移）。
"""
import numpy as np, json, time, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(OUTDIR, "xlii_s0_v3.json")
FIG1 = os.path.join(OUTDIR, "xlii_s0_fig1.png")
FIG2 = os.path.join(OUTDIR, "xlii_s0_fig2.png")
T = 6.0e5
LOW = 300.0
SEGS = [(300, 1.2e5), (1.2e5, 2.4e5), (2.4e5, 3.6e5), (3.6e5, 4.8e5), (4.8e5, 6.0e5)]
plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei"]
plt.rcParams["axes.unicode_minus"] = False


def sinc(x):
    with np.errstate(divide="ignore", invalid="ignore"):
        x = np.asarray(x, dtype=float)
        return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)


def rho_zeta(t):
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    return np.log(t / (2 * np.pi)) / (2 * np.pi)


def rho_L(t, minus1=True):
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    c = -1.0 if minus1 else 0.0
    return (np.log(t / (2 * np.pi)) + np.log(5.0) + c) / (2 * np.pi)


def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2


def pair_hist_local(z, rho_fn, half, binw):
    """局部归一化配对直方图：u=|Δ|·ρ(t_mid)∈(0,half]。rho_fn(t) 逐点密度（已校准）。"""
    n = len(z)
    nb = int(np.ceil(half / binw)) + 1
    hist = np.zeros(nb, dtype=np.float64)
    win_raw = half / 0.5
    chunk = 200000
    for a0 in range(0, n, chunk):
        a1 = min(a0 + chunk, n)
        za = z[a0:a1]
        lo = np.searchsorted(z, za - win_raw, side="left")
        hi = np.searchsorted(z, za + win_raw, side="right")
        segs = []
        for i in range(a1 - a0):
            L, H = lo[i], hi[i]
            if H - L > 1:
                segs.append((np.abs(z[L:H] - za[i]), 0.5 * (za[i] + z[L:H])))
        if not segs:
            continue
        ds = np.concatenate([s[0] for s in segs])
        tm = np.concatenate([s[1] for s in segs])
        u = ds * rho_fn(tm)
        u = u[(u > 1e-12) & (u < half)]
        hist += np.histogram(u, bins=nb, range=(0.0, half))[0]
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist, n


def A_from_hist(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n


def gue2_a(a, R=60.0):
    """有序全对 GUE：A=1+2∫₀^R (1−sinc²(πu))·sinc⁴(πu/a)du。"""
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    integ = (1.0 - sinc(np.pi * u) ** 2) * sinc(np.pi * u / a) ** 4
    return 1.0 + 2.0 * float(np.trapezoid(integ, u))


def poi2_a(a, R=60.0):
    """有序全对 Poisson：A=1+2∫₀^R sinc⁴(πu/a)du（R→∞ → 1+2a/3）。"""
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    return 1.0 + 2.0 * float(np.trapezoid(sinc(np.pi * u / a) ** 4, u))


def nn_mean_block(arr, rho_fn):
    dnn = np.diff(arr); dnn = dnn[dnn > 0]
    tm = 0.5 * (arr[:-1] + arr[1:])
    s = dnn * rho_fn(tm)
    return float(np.mean(s)), float(np.var(s))


def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)

    # ---- L 密度校准：−1 vs 去−1 ----
    cal = {}
    for tag, fn in (("minus1", lambda t: rho_L(t, True)), ("no_minus1", lambda t: rho_L(t, False))):
        m, v = nn_mean_block(l, fn)
        cal[tag] = {"nn_mean": m, "nn_var": v}
    zcal = {"zeta": nn_mean_block(z, rho_zeta)}
    print("L 密度校准:", {k: round(v["nn_mean"], 4) for k, v in cal.items()},
          " ζ:", round(zcal["zeta"][0], 4))
    rhoL = lambda t: rho_L(t, False)   # 去−1（若 nn_mean 更接近 1 则采用）

    # ---- 主曲线：局部口径 ----
    A_GRID = [0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.75,
              1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]
    half_w, binw_w = 40.0, 0.02
    uc_w, hz_w, nz_ = pair_hist_local(z, rho_zeta, half_w, binw_w)
    uc_w, hl_w, nl_ = pair_hist_local(l, rhoL, half_w, binw_w)
    half_f, binw_f = 8.0, 0.002
    uc_f, hz_f, _ = pair_hist_local(z, rho_zeta, half_f, binw_f)
    uc_f, hl_f, _ = pair_hist_local(l, rhoL, half_f, binw_f)
    print("local histograms done %.1fs" % (time.time() - t0))

    A_zeta = {a: A_from_hist(hz_w, uc_w, nz_, a) for a in A_GRID}
    A_L = {a: A_from_hist(hl_w, uc_w, nl_, a) for a in A_GRID}
    A_zeta_f = {a: (A_from_hist(hz_f, uc_f, nz_, a) if a <= 0.5 else A_zeta[a]) for a in A_GRID}
    A_L_f = {a: (A_from_hist(hl_f, uc_f, nl_, a) if a <= 0.5 else A_L[a]) for a in A_GRID}
    G2 = {a: gue2_a(a) for a in A_GRID}
    P2 = {a: poi2_a(a) for a in A_GRID}

    # ---- 全局 δ 口径（audit6 复现，口径差报告）----
    delta = np.log(T) / (2 * np.pi)
    nb = int(np.ceil(half_w * delta / binw_w)) + 1
    def pair_hist_global(arr, half, binw, delta):
        n = len(arr); nb_ = int(np.ceil(half * delta / binw)) + 1
        hist = np.zeros(nb_)
        chunk = 300000
        for a0 in range(0, n, chunk):
            a1 = min(a0 + chunk, n)
            za = arr[a0:a1]
            lo = np.searchsorted(arr, za - half, side="left")
            hi = np.searchsorted(arr, za + half, side="right")
            segs = []
            for i in range(a1 - a0):
                L, H = lo[i], hi[i]
                if H - L > 1:
                    segs.append(np.abs(arr[L:H] - za[i]))
            if not segs:
                continue
            ds = np.concatenate(segs); ds = ds[ds > 1e-12]
            hist += np.histogram(ds * delta, bins=nb_, range=(0.0, half * delta))[0]
        uc_ = (np.arange(nb_) + 0.5) * binw
        return uc_, hist
    uc_g, hz_g = pair_hist_global(z, half_w, binw_w, delta)
    uc_g, hl_g = pair_hist_global(l, half_w, binw_w, delta)
    A_delta = {"zeta_a0.5": A_from_hist(hz_g, uc_g, nz_, 0.5),
               "zeta_a1.0": A_from_hist(hz_g, uc_g, nz_, 1.0),
               "L_a0.5": A_from_hist(hl_g, uc_g, nl_, 0.5),
               "L_a1.0": A_from_hist(hl_g, uc_g, nl_, 1.0)}
    print("全局δ口径（audit6 复现）:", {k: round(v, 5) for k, v in A_delta.items()},
          "（audit6: ζ a0.5=1.00789 a1.0=1.05647; L 1.01138/1.08071）")

    # ---- 极小间距（校准后 ρ）----
    def min_gap(arr, rho_fn):
        dnn = np.diff(arr); dnn = dnn[dnn > 0]
        tm = 0.5 * (arr[:-1] + arr[1:])
        s = dnn * rho_fn(tm)
        cnt = {e: int(np.sum(s < e)) for e in [0.05, 0.01, 0.005, 0.001]}
        gue = {e: round((32.0 / (3 * np.pi ** 2)) * e ** 3 * len(arr), 1) for e in [0.05, 0.01, 0.005, 0.001]}
        return {"n": len(arr), "s_min": float(np.min(s)), "counts": cnt, "gue_pred": gue}
    mg = {"zeta": min_gap(z, rho_zeta), "L": min_gap(l, rhoL)}

    # ---- 段间漂移（局部口径，校准后）----
    SEG_A = [0.3, 0.5, 1.0, 2.0]
    seg_res = {}
    for (lo_, hi_) in SEGS:
        key = "%d-%d" % (lo_, hi_)
        seg_res[key] = {}
        for fam, arr, rfn in (("zeta", z, rho_zeta), ("L", l, rhoL)):
            seg = arr[(arr >= lo_) & (arr < hi_)]
            ns = len(seg)
            uc_s, h_s, _ = pair_hist_local(seg, rfn, half_w, binw_w)
            seg_res[key][fam] = {"n": ns, "A": {str(a): A_from_hist(h_s, uc_s, ns, a) for a in SEG_A}}
    drift = {}
    for fam in ("zeta", "L"):
        fd = {}
        for a in SEG_A:
            vals = [seg_res[k][fam]["A"][str(a)] for k in seg_res]
            fd[str(a)] = {"vals": [round(v, 6) for v in vals],
                          "max_adj": round(max(abs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1)), 6),
                          "range": round(max(vals) - min(vals), 6)}
        drift[fam] = fd

    # ---- 判定 ----
    keys_n = sorted([a for a in A_GRID if a <= 0.5])
    verdict = {
        "zeta_narrow_Aminus1": [round(A_zeta_f[a] - 1.0, 6) for a in keys_n],
        "L_narrow_Aminus1": [round(A_L_f[a] - 1.0, 6) for a in keys_n],
        "zeta_dev_vs_GUE2": {str(a): round(A_zeta_f[a] - G2[a], 5) for a in A_GRID},
        "L_dev_vs_GUE2": {str(a): round(A_L_f[a] - G2[a], 5) for a in A_GRID},
        "zeta_monotone_to1": all(A_zeta_f[a] < A_zeta_f[a2] for a, a2 in zip(keys_n[:-1], keys_n[1:])),
        "L_monotone_to1": all(A_L_f[a] < A_L_f[a2] for a, a2 in zip(keys_n[:-1], keys_n[1:])),
        "note": "判定：窄端单调→1；全曲线 vs 双侧 GUE 偏差在段间漂移内=数据支持全尺度 GUE；超漂移=结构信号",
    }

    out = {"meta": {"T": T, "LOW": LOW, "nz": nz, "nl": nl,
                    "口径": "局部归一化 u=Δ·ρ(t_mid)，有序全对（i≠j 两侧），GUE/Poisson 双侧因子 2",
                    "L_density_cal": cal, "zeta_nn_mean": zcal["zeta"][0]},
           "lambda_eff": {str(a): round(np.pi / a, 4) for a in A_GRID},
           "A_zeta": {str(a): round(v, 6) for a, v in A_zeta.items()},
           "A_L": {str(a): round(v, 6) for a, v in A_L.items()},
           "A_zeta_fine": {str(a): round(v, 6) for a, v in A_zeta_f.items()},
           "A_L_fine": {str(a): round(v, 6) for a, v in A_L_f.items()},
           "A_GUE2": {str(a): round(v, 6) for a, v in G2.items()},
           "A_Poisson2": {str(a): round(v, 6) for a, v in P2.items()},
           "A_delta_global": {k: round(v, 6) for k, v in A_delta.items()},
           "min_gap": mg, "drift": drift, "verdict": verdict,
           "elapsed": time.time() - t0}
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)

    # ---- 打印 ----
    print("\n--- A(λ) 局部口径 vs 双侧 GUE/Poisson ---")
    print("%-6s %-7s %-9s %-9s %-9s %-9s %-9s" % ("a", "λeff", "Aζ", "AL", "GUE2", "Poi2", "ζ−GUE2"))
    for a in A_GRID:
        print("%-6.2f %-7.2f %-9.5f %-9.5f %-9.5f %-9.5f %-9.5f"
              % (a, np.pi / a, A_zeta_f[a], A_L_f[a], G2[a], P2[a], A_zeta_f[a] - G2[a]))
    print("\n--- 极小间距 ---")
    for fam in ("zeta", "L"):
        g = mg[fam]
        print("%s: s_min=%.5f 计数=%s GUE预测=%s" % (fam, g["s_min"], g["counts"], g["gue_pred"]))
    print("\n--- 段间漂移（局部口径）---")
    for fam in ("zeta", "L"):
        for a in SEG_A:
            df_ = drift[fam][str(a)]
            print("%s a=%.1f: %s 相邻max=%.5f 极差=%.5f" % (fam, a, df_["vals"], df_["max_adj"], df_["range"]))
    print("\n--- 判定 ---")
    print("ζ 窄端单调→1: %s, A−1=%s" % (verdict["zeta_monotone_to1"], verdict["zeta_narrow_Aminus1"]))
    print("L 窄端单调→1: %s, A−1=%s" % (verdict["L_monotone_to1"], verdict["L_narrow_Aminus1"]))
    print("ζ 偏差 vs GUE2（窄端）:", {k: verdict["zeta_dev_vs_GUE2"][k] for k in [str(x) for x in keys_n]})
    print("ζ 偏差 vs GUE2（宽端）:", {k: verdict["zeta_dev_vs_GUE2"][k] for k in ["2.0", "4.0", "8.0"]})
    print("L 偏差 vs GUE2（宽端）:", {k: verdict["L_dev_vs_GUE2"][k] for k in ["2.0", "4.0", "8.0"]})
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
