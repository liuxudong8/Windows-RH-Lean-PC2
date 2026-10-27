# -*- coding: utf-8 -*-
"""攻防 XLII · S0 数值定向：全尺度 GUE 配对（干到 1）的生死门判定。

目标（四件事一次钉死）：
① 核参数 a ↔ 谱支撑 λ_eff 换算：K_fejer(u,a)=sinc²(πu/a)，其 Fourier 谱支撑（关于 u 的频域变量 ξ，
   e^{-2πiuξ} 约定）为 |ξ|<π/a，即 λ_eff(a)=π/a。注：文献/文档此前"fejer_a0.5 谱支撑 λ_eff≈0.5"
   为倒挂口径——λ_eff=0.5 对应 a=π/0.5≈6.28。输出换算表钉死。
② A(λ) 全曲线：a∈{0.1,…,8}（λ_eff∈{31.4,…,0.39}），测 A_ζ、A_L（fejer 核，audit6 同口径 half=40,
   binw=0.02 复现 + 细网格 binw=0.002 校正 a≤0.5），并对照 GUE 预测
   A_GUE(a)=1+∫(1−sinc²(πu))·sinc⁴(πu/a)du 与 Poisson 基线 1+a/3。
   判定：实测是否单调逼近 1、无反弹；窄端/宽端相对 GUE 的偏差（长程结构信号）。
③ 重零点/极小间距探测：全局归一化最近邻 s_min、s<ε (ε=0.01/0.005/0.001) 计数 vs GUE
   ∫₀^ε (32/π²)s²ds = (32/(3π²))ε³·N（重零点密度上界）。
④ A(λ) 有限 T 涨落标定：5 段子区间 × a∈{0.3,0.5,1.0,2.0}，A 段间漂移（判定窄端信号是否被涨落淹没）。

输出 xlii_s0.json + xlii_s0_fig1.png（A(λ) 实测 vs GUE/Poisson）+ xlii_s0_fig2.png（A−1 对数-对数收敛 + 段间漂移）。
Anaconda python（numpy/scipy/matplotlib）。
"""
import numpy as np, json, time, os
from scipy.integrate import quad

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(OUTDIR, "xlii_s0.json")
T = 6.0e5
LOW = 300.0
SEGS = [(300, 1.2e5), (1.2e5, 2.4e5), (2.4e5, 3.6e5), (3.6e5, 4.8e5), (4.8e5, 6.0e5)]


def sinc(x):
    x = np.asarray(x, dtype=float)
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)


def rho_fun(t, is_L):
    """零点密度：ζ 与 L(χ₅)。L 含模因子：ρ=(1/2π)[log(t/2π)+log q −1]（audit1 口径）。"""
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    base = np.log(t / (2 * np.pi))
    if is_L:
        base = base + np.log(5.0) - 1.0
    return base / (2 * np.pi)


def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2


def pair_hist(z, delta, half, binw):
    """配对间距直方图（audit6 同口径）：分块 searchsorted，|Δ|∈(0,half]，u=δΔ。"""
    n = len(z)
    nb = int(np.ceil(half * delta / binw)) + 1
    hist = np.zeros(nb, dtype=np.float64)
    chunk = 300000
    for a0 in range(0, n, chunk):
        a1 = min(a0 + chunk, n)
        za = z[a0:a1]
        lo = np.searchsorted(z, za - half, side="left")
        hi = np.searchsorted(z, za + half, side="right")
        segs = []
        for i in range(a1 - a0):
            L, H = lo[i], hi[i]
            if H - L > 1:
                segs.append(np.abs(z[L:H] - za[i]))
        if not segs:
            continue
        ds = np.concatenate(segs)
        ds = ds[ds > 1e-12]
        hist += np.histogram(ds * delta, bins=nb, range=(0.0, half * delta))[0]
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist


def A_from_hist(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n


def gue_a(a, R=60.0):
    """GUE 二点相关 ρ₂(u)=1−sinc²(πu) 下的配对常数：A=1+∫₀^R (1−sinc²(πu))·sinc⁴(πu/a) du。"""
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    integ = (1.0 - sinc(np.pi * u) ** 2) * sinc(np.pi * u / a) ** 4
    return 1.0 + float(np.trapezoid(integ, u))


def A_poisson(a, R=60.0):
    """泊松（随机）二点相关 ρ₂=1：A=1+∫₀^R sinc⁴(πu/a)du，R→∞ 时 =1+a/3。"""
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    return 1.0 + float(np.trapezoid(sinc(np.pi * u / a) ** 4, u))


def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    delta = np.log(T) / (2.0 * np.pi)
    print("T=%.0f nz=%d nl=%d δ=%.6f" % (T, nz, nl, delta))

    # ---- ① λ_eff 换算表 ----
    A_GRID = [0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.75,
              1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]
    lam_eff = {str(a): round(np.pi / a, 4) for a in A_GRID}

    # ---- ② A(λ) 全曲线：宽直方图（复现 audit6）+ 细直方图（a≤0.5 校正）----
    half_w, binw_w = 40.0, 0.02
    uc_w, hz_w = pair_hist(z, delta, half_w, binw_w)
    uc_w, hl_w = pair_hist(l, delta, half_w, binw_w)
    half_f, binw_f = 8.0, 0.002
    uc_f, hz_f = pair_hist(z, delta, half_f, binw_f)
    uc_f, hl_f = pair_hist(l, delta, half_f, binw_f)
    print("histograms done %.1fs" % (time.time() - t0))

    A_zeta, A_L = {}, {}
    A_zeta_fine, A_L_fine = {}, {}
    for a in A_GRID:
        A_zeta[a] = A_from_hist(hz_w, uc_w, nz, a)
        A_L[a] = A_from_hist(hl_w, uc_w, nl, a)
        if a <= 0.5:
            A_zeta_fine[a] = A_from_hist(hz_f, uc_f, nz, a)
            A_L_fine[a] = A_from_hist(hl_f, uc_f, nl, a)
        else:
            A_zeta_fine[a] = A_zeta[a]
            A_L_fine[a] = A_L[a]

    # GUE / Poisson 对照曲线
    A_gue = {str(a): gue_a(a) for a in A_GRID}
    A_poi = {str(a): A_poisson(a) for a in A_GRID}
    # 截断效应估计：GUE 积分 R=40（宽直方图 half）vs R=60
    A_gue_R40 = {str(a): gue_a(a, R=40.0) for a in A_GRID}
    trunc = {str(a): A_gue[str(a)] - A_gue_R40[str(a)] for a in A_GRID}

    # ---- ③ 极小间距 / 重零点密度上界 ----
    def min_gap_block(arr, is_L):
        dnn = np.diff(arr)
        dnn = dnn[dnn > 0]
        tmid = 0.5 * (arr[:-1] + arr[1:])
        s = dnn * rho_fun(tmid, is_L)
        n = len(arr)
        eps_list = [0.05, 0.01, 0.005, 0.001]
        cnt = {("s<%.3f" % e): int(np.sum(s < e)) for e in eps_list}
        gue_pred = {("gue_%.3f" % e): round((32.0 / (3.0 * np.pi ** 2)) * e ** 3 * n, 1)
                    for e in eps_list}
        return {"n": n, "s_min": float(np.min(s)), "s_min_idx": int(np.argmin(s)),
                "counts": cnt, "gue_pred_counts": gue_pred}

    mg = {"zeta": min_gap_block(z, False), "L": min_gap_block(l, True)}

    # ---- ④ 子区间涨落标定 ----
    SEG_A = [0.3, 0.5, 1.0, 2.0]
    seg_res = {}
    for (lo_, hi_) in SEGS:
        key = "%d-%d" % (lo_, hi_)
        seg_res[key] = {}
        for fam, arr, isL in (("zeta", z, False), ("L", l, True)):
            seg = arr[(arr >= lo_) & (arr < hi_)]
            nseg = len(seg)
            uc_s, h_s = pair_hist(seg, delta, half_w, binw_w)
            seg_res[key][fam] = {"n": nseg,
                                 "A": {str(a): A_from_hist(h_s, uc_s, nseg, a) for a in SEG_A}}

    # 漂移统计：相邻段间最大差 + 全程极差
    drift = {}
    for fam in ("zeta", "L"):
        fam_drift = {}
        for a in SEG_A:
            vals = [seg_res[k][fam]["A"][str(a)] for k in seg_res]
            fam_drift[str(a)] = {"vals": [round(v, 6) for v in vals],
                                 "max_adj": round(max(abs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1)), 6),
                                 "range": round(max(vals) - min(vals), 6)}
        drift[fam] = fam_drift

    # ---- 判定汇总 ----
    def monotone_narrow(A_dict):
        """a 从 0.5 向 0.1：A 是否单调下降（→1）。"""
        keys = sorted([a for a in A_dict if a <= 0.5])
        vals = [A_dict[a] for a in keys]
        return {"a_seq": keys, "A_seq": [round(v, 5) for v in vals],
                "strictly_decreasing": all(vals[i + 1] < vals[i] for i in range(len(vals) - 1))}

    verdict = {
        "zeta_narrow": monotone_narrow(A_zeta_fine),
        "L_narrow": monotone_narrow(A_L_fine),
        "zeta_dev_vs_gue_narrow": {str(a): round(A_zeta_fine[a] - A_gue[str(a)], 5) for a in A_GRID if a <= 0.5},
        "zeta_dev_vs_gue_wide": {str(a): round(A_zeta[a] - A_gue[str(a)], 5) for a in A_GRID if a >= 2.0},
        "L_dev_vs_gue_narrow": {str(a): round(A_L_fine[a] - A_gue[str(a)], 5) for a in A_GRID if a <= 0.5},
        "L_dev_vs_gue_wide": {str(a): round(A_L[a] - A_gue[str(a)], 5) for a in A_GRID if a >= 2.0},
    }

    out = {
        "meta": {"T": T, "LOW": LOW, "delta": delta, "nz": nz, "nl": nl,
                 "half_w": half_w, "binw_w": binw_w, "half_f": half_f, "binw_f": binw_f},
        "lambda_eff": lam_eff,
        "A_zeta": {str(a): round(v, 6) for a, v in A_zeta.items()},
        "A_L": {str(a): round(v, 6) for a, v in A_L.items()},
        "A_zeta_fine": {str(a): round(v, 6) for a, v in A_zeta_fine.items()},
        "A_L_fine": {str(a): round(v, 6) for a, v in A_L_fine.items()},
        "A_gue": {str(a): round(v, 6) for a, v in A_gue.items()},
        "A_gue_trunc_R40": trunc,
        "A_poisson": {str(a): round(v, 6) for a, v in A_poi.items()},
        "min_gap": mg,
        "segs": seg_res,
        "drift": drift,
        "verdict": verdict,
        "elapsed": time.time() - t0,
    }
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)

    # ---- 打印 ----
    print("\n--- ① λ_eff(a)=π/a 换算表 ---")
    print(" ".join("a=%.2f→λ=%.2f" % (a, np.pi / a) for a in [0.1, 0.25, 0.5, 1.0, 2.0, 6.283]))
    print("\n--- ② A(λ) 全曲线（细网格 a≤0.5）---")
    print("%-6s %-10s %-10s %-10s %-10s %-10s" % ("a", "Aζ", "AL", "GUEζ≈", "GUE", "Poisson"))
    for a in A_GRID:
        print("%-6.2f %-10.5f %-10.5f %-10.5f %-10.5f %-10.5f"
              % (a, A_zeta_fine[a], A_L_fine[a], A_gue[str(a)], A_gue[str(a)], A_poi[str(a)]))
    print("\n--- ③ 极小间距/重零点 ---")
    for fam in ("zeta", "L"):
        g = mg[fam]
        print("%s: n=%d s_min=%.5f (idx %d) %s" % (fam, g["n"], g["s_min"], g["s_min_idx"], g["counts"]))
        print("   GUE 预测: %s" % g["gue_pred_counts"])
    print("\n--- ④ 段间漂移 ---")
    for fam in ("zeta", "L"):
        for a in SEG_A:
            df_ = drift[fam][str(a)]
            print("%s a=%.1f: 全段 %s 相邻max=%.5f 极差=%.5f"
                  % (fam, a, df_["vals"], df_["max_adj"], df_["range"]))
    print("\n--- 判定 ---")
    print("ζ 窄端单调→1: %s (A= %s)" % (verdict["zeta_narrow"]["strictly_decreasing"],
                                          verdict["zeta_narrow"]["A_seq"]))
    print("L 窄端单调→1: %s (A= %s)" % (verdict["L_narrow"]["strictly_decreasing"],
                                          verdict["L_narrow"]["A_seq"]))
    print("ζ 窄端偏差 vs GUE: %s" % verdict["zeta_dev_vs_gue_narrow"])
    print("L 窄端偏差 vs GUE: %s" % verdict["L_dev_vs_gue_narrow"])
    print("ζ 宽端偏差 vs GUE: %s" % verdict["zeta_dev_vs_gue_wide"])
    print("L 宽端偏差 vs GUE: %s" % verdict["L_dev_vs_gue_wide"])
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
