# -*- coding: utf-8 -*-
"""攻防 XLII · S0 数值定向 v2：局部归一化口径（修正全局 δ 伪影）。

v1 发现：audit6/8 配对和用全局 δ=logT/(2π) 归一化，但零点密度随高度变化
（t∈[300,6e5]，ρ 从 0.61 到 1.83），实测 u=δΔ 平均值≈1.74≠1——窄核被窗过滤
看不出，宽核（a≥2）放大尺度误差，产生"实测超 GUE 甚至超 Poisson"的伪上偏。

v2 主口径：局部归一化 u=|Δ|·ρ(t_mid)，t_mid=(γ_i+γ_j)/2，ρ 逐点。
- ζ：nn_mean=1.0000（audit8，s=Δ·ρ(tmid)），该口径精确。
- L：nn_mean=0.92 → ρ_L 公式常数项疑似有误（−1/(2π) 项？），附 10 段密度校准表。
- GUE 预测 A_GUE(a)=1+∫(1−sinc²(πu))·sinc⁴(πu/a)du 与 Poisson 1+a/3 均按 u 平均=1。

输出 xlii_s0_v2.json + 图（fig1 A(λ) vs GUE/Poisson 双族；fig2 A−1 对数-对数 + 段间漂移）。
"""
import numpy as np, json, time, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(OUTDIR, "xlii_s0_v2.json")
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


def rho_fun(t, is_L):
    """零点密度：ζ 与 L(χ₅)。L 含模因子：ρ=(1/2π)[log(t/2π)+log q −1]（audit1 口径，v2 校准报告）。"""
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    base = np.log(t / (2 * np.pi))
    if is_L:
        base = base + np.log(5.0) - 1.0
    return base / (2 * np.pi)


def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2


def pair_hist_local(z, is_L, half, binw):
    """局部归一化配对直方图：u=|Δ|·ρ((γ_i+γ_j)/2)∈(0,half]。窗口按 ρ_min 保守扩大。"""
    n = len(z)
    nb = int(np.ceil(half / binw)) + 1
    hist = np.zeros(nb, dtype=np.float64)
    # ρ 最小下界（t≥LOW）：ζ ρ≈0.615、L ρ≈0.712；保守用 0.5
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
        u = ds * rho_fun(tm, is_L)
        u = u[(u > 1e-12) & (u < half)]
        hist += np.histogram(u, bins=nb, range=(0.0, half))[0]
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist


def A_from_hist(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n


def gue_a(a, R=60.0):
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    integ = (1.0 - sinc(np.pi * u) ** 2) * sinc(np.pi * u / a) ** 4
    return 1.0 + float(np.trapezoid(integ, u))


def poi_a(a, R=60.0):
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    return 1.0 + float(np.trapezoid(sinc(np.pi * u / a) ** 4, u))


def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    print("T=%.0f nz=%d nl=%d" % (T, nz, nl))

    # ---- L 密度校准：10 段 nn_mean ----
    cal = {}
    edges = np.linspace(LOW, T, 11)
    for k in range(10):
        lo_, hi_ = edges[k], edges[k + 1]
        seg_l = l[(l >= lo_) & (l < hi_)]
        if len(seg_l) > 50:
            dnn = np.diff(seg_l); dnn = dnn[dnn > 0]
            tm = 0.5 * (seg_l[:-1] + seg_l[1:])
            s = dnn * rho_fun(tm, True)
            cal["seg%d" % k] = {"t": [lo_, hi_], "n": int(len(seg_l)),
                                "nn_mean": float(np.mean(s))}
    print("L 密度校准 nn_mean:", {k: round(v["nn_mean"], 4) for k, v in cal.items()})

    # ---- 主口径：局部归一化全曲线 ----
    A_GRID = [0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.75,
              1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]
    half_w, binw_w = 40.0, 0.02
    uc_w, hz_w = pair_hist_local(z, False, half_w, binw_w)
    uc_w, hl_w = pair_hist_local(l, True, half_w, binw_w)
    half_f, binw_f = 8.0, 0.002
    uc_f, hz_f = pair_hist_local(z, False, half_f, binw_f)
    uc_f, hl_f = pair_hist_local(l, True, half_f, binw_f)
    print("local histograms done %.1fs" % (time.time() - t0))

    A_zeta = {a: A_from_hist(hz_w, uc_w, nz, a) for a in A_GRID}
    A_L = {a: A_from_hist(hl_w, uc_w, nl, a) for a in A_GRID}
    A_zeta_f = {a: (A_from_hist(hz_f, uc_f, nz, a) if a <= 0.5 else A_zeta[a]) for a in A_GRID}
    A_L_f = {a: (A_from_hist(hl_f, uc_f, nl, a) if a <= 0.5 else A_L[a]) for a in A_GRID}
    A_gue = {a: gue_a(a) for a in A_GRID}
    A_poi = {a: poi_a(a) for a in A_GRID}

    # ---- 段间漂移（局部口径）----
    SEG_A = [0.3, 0.5, 1.0, 2.0]
    seg_res = {}
    for (lo_, hi_) in SEGS:
        key = "%d-%d" % (lo_, hi_)
        seg_res[key] = {}
        for fam, arr, isL in (("zeta", z, False), ("L", l, True)):
            seg = arr[(arr >= lo_) & (arr < hi_)]
            nseg = len(seg)
            uc_s, h_s = pair_hist_local(seg, isL, half_w, binw_w)
            seg_res[key][fam] = {"n": nseg,
                                 "A": {str(a): A_from_hist(h_s, uc_s, nseg, a) for a in SEG_A}}
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
    def dev_report(fam_fine, fam_wide, fam):
        return {"narrow": {str(a): round(fam_fine[a] - A_gue[a], 5) for a in keys_n},
                "wide": {str(a): round(fam_wide[a] - A_gue[a], 5) for a in A_GRID if a >= 2.0}}
    verdict = {
        "zeta": dev_report(A_zeta_f, A_zeta, "zeta"),
        "L": dev_report(A_L_f, A_L, "L"),
        "zeta_A_seq_narrow": [round(A_zeta_f[a], 5) for a in keys_n],
        "L_A_seq_narrow": [round(A_L_f[a], 5) for a in keys_n],
        "note": "判定：窄端偏差在段间漂移内=通过；宽端偏差超漂移=长程结构信号",
    }

    out = {"meta": {"T": T, "LOW": LOW, "nz": nz, "nl": nl, "口径": "局部归一化 u=|Δ|·ρ(t_mid)"},
           "L_density_cal": {k: {"nn_mean": v["nn_mean"], "n": v["n"]} for k, v in cal.items()},
           "A_zeta": {str(a): round(v, 6) for a, v in A_zeta.items()},
           "A_L": {str(a): round(v, 6) for a, v in A_L.items()},
           "A_zeta_fine": {str(a): round(v, 6) for a, v in A_zeta_f.items()},
           "A_L_fine": {str(a): round(v, 6) for a, v in A_L_f.items()},
           "A_gue": {str(a): round(v, 6) for a, v in A_gue.items()},
           "A_poisson": {str(a): round(v, 6) for a, v in A_poi.items()},
           "lambda_eff": {str(a): round(np.pi / a, 4) for a in A_GRID},
           "drift": drift, "verdict": verdict, "elapsed": time.time() - t0}
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)

    # ---- 打印 ----
    print("\n--- 局部口径 A(λ) 全曲线 ---")
    print("%-6s %-10s %-10s %-10s %-10s %-10s %-10s" % ("a", "λeff", "Aζ", "AL", "GUE", "Poisson", "ζ−GUE"))
    for a in A_GRID:
        print("%-6.2f %-10.2f %-10.5f %-10.5f %-10.5f %-10.5f %-10.5f"
              % (a, np.pi / a, A_zeta_f[a], A_L_f[a], A_gue[a], A_poi[a], A_zeta_f[a] - A_gue[a]))
    print("\n--- 段间漂移（局部口径）---")
    for fam in ("zeta", "L"):
        for a in SEG_A:
            df_ = drift[fam][str(a)]
            print("%s a=%.1f: 全段 %s 相邻max=%.5f 极差=%.5f" % (fam, a, df_["vals"], df_["max_adj"], df_["range"]))
    print("\n--- 判定 ---")
    for fam in ("zeta", "L"):
        v = verdict[fam]
        print("%s 窄端偏差 vs GUE: %s" % (fam, v["narrow"]))
        print("%s 宽端偏差 vs GUE: %s" % (fam, v["wide"]))
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
