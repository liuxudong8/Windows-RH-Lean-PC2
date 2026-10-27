# -*- coding: utf-8 -*-
"""攻防 XLII · S2(ii)：跨 T 衰减律判别——配对常数 A(λ;T) 对 T 的衰减律
（BGS 误差项 1/√logT vs 离线口径 1/logT），决定 S1b 速率 (logT)^{−15/7} 是否升级。

口径（与 S0/S1a 一致）：fejer 核 K=sinc²(πu/a)，half=40, binw=0.02 全局配对直方图；
GUE2 基准 gue2_a(a)=1+2∫₀^R (1−sinc²πu)·sinc⁴(πu/a)du（有序对口径）。
统一截断 [LOW,T]，LOW=300（与 S0 同）。跨 T 档：
  T=1e4: zeta_T10000 + L_D5_T1e4
  T=2e4: zeros_v2（双键 zeta/L）
  T=4e4: zeta_T40000 + L_D5_TT4e4
  T=6e5: zeros_T6e5（双键）
判别：对每个 a∈{0.3,0.5,1.0,2.0}、每族，Δ=A−GUE2 对 x∈{1/√logT, 1/logT} 线性拟合，
比较 R² 与斜率符号稳定性。新四档（1e5/2e5/4e5/8e5）生成后 rerun 升级判定。
"""
import numpy as np, json, time, os

BASE = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(OUTDIR, "xlii_s2ii.json")
FIG = os.path.join(OUTDIR, "xlii_s2ii_fig.png")

TABS = [
    # (T, zeta_npz, L_npz)
    (1.0e4, "zeta_T10000.npz", "L_D5_T1e4.npz"),
    (2.0e4, "zeros_v2.npz", "zeros_v2.npz"),
    (4.0e4, "zeta_T40000.npz", "L_D5_TT4e4.npz"),
    (1.0e5, "zeta_T100000.npz", "L_D5_T100000.npz"),
    (2.0e5, "zeta_T200000.npz", "L_D5_T200000.npz"),
    (4.0e5, "zeta_T400000.npz", "L_D5_T400000.npz"),
    (6.0e5, "zeros_T6e5.npz", "zeros_T6e5.npz"),
    (8.0e5, "zeta_T800000.npz", "L_D5_T800000.npz"),
]
LOW = 300.0
A_GRID = ["0.1", "0.2", "0.3", "0.5", "1.0", "2.0"]


def sinc(x):
    x = np.asarray(x, dtype=float)
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)


def rho_zeta(t):
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    return np.log(t / (2 * np.pi)) / (2 * np.pi)


def rho_L(t):
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    return (np.log(t / (2 * np.pi)) + np.log(5.0)) / (2 * np.pi)


def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2


def pair_hist(z, delta, half, binw):
    """S0 同口径：全局归一化（统一密度 δ），分块 searchsorted。"""
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


def gue2_a(a, R=60.0):
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    return 1.0 + 2.0 * float(np.trapezoid((1.0 - sinc(np.pi * u) ** 2) * sinc(np.pi * u / a) ** 4, u))


def main():
    t0 = time.time()
    half, binw = 40.0, 0.02
    gue2 = {a: gue2_a(float(a)) for a in A_GRID}
    rows = []          # per-T 记录
    fit_data = {}      # (fam, a) -> list of (logT, Delta)
    for (T, zf, lf) in TABS:
        z = np.sort(np.load(os.path.join(BASE, zf))["zeta"])
        l = np.sort(np.load(os.path.join(BASE, lf))["L"])
        z = z[(z >= LOW) & (z <= T)]
        l = l[(l >= LOW) & (l <= T)]
        nz, nl = len(z), len(l)
        dz = rho_zeta(np.median(z)) if nz else np.nan
        dl = rho_L(np.median(l)) if nl else np.nan
        A = {"zeta": {}, "L": {}}
        for tag, arr, dlt in (("zeta", z, dz), ("L", l, dl)):
            uc, hist = pair_hist(arr, dlt, half, binw)
            for a in A_GRID:
                A[tag][a] = round(A_from_hist(hist, uc, len(arr), float(a)), 6)
        rows.append({"T": T, "n_zeta": nz, "n_L": nl, "A": A})
        for tag in ("zeta", "L"):
            for a in A_GRID:
                fit_data.setdefault((tag, a), []).append((np.log(T), A[tag][a] - gue2[a]))
        print("T=%.0e  nz=%d  nl=%d  %.0fs" % (T, nz, nl, time.time() - t0), flush=True)

    # ---- 判别拟合 ----
    fits = {}
    for (tag, a), pts in fit_data.items():
        lts = np.array([p[0] for p in pts]); Ds = np.array([p[1] for p in pts])
        fits.setdefault(tag, {})[a] = {}
        for law, xf in (("1_over_sqrtlogT", lambda t: 1.0 / np.sqrt(t)),
                        ("1_over_logT", lambda t: 1.0 / t)):
            x = xf(lts)
            k, b = np.polyfit(x, Ds, 1)
            pred = k * x + b
            ss_res = float(np.sum((Ds - pred) ** 2))
            ss_tot = float(np.sum((Ds - Ds.mean()) ** 2))
            r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0
            fits[tag][a][law] = {"slope": round(float(k), 6), "intercept": round(float(b), 6),
                                 "r2": round(float(r2), 4)}
    # 每 (a,law) 跨族汇总
    law_tally = {}
    for a in A_GRID:
        law_tally[a] = {}
        for law in ("1_over_sqrtlogT", "1_over_logT"):
            r2z = fits["zeta"][a][law]["r2"]; r2l = fits["L"][a][law]["r2"]
            law_tally[a][law] = {"r2_zeta": r2z, "r2_L": r2l, "r2_mean": round(0.5 * (r2z + r2l), 4)}

    res = {"meta": {"LOW": LOW, "half": half, "binw": binw, "A_grid": A_GRID,
                    "gue2": gue2, "tabs": len(TABS)},
           "rows": rows, "fits": fits, "law_tally": law_tally}
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(res, f, ensure_ascii=False, indent=1)
    print("saved:", OUT)

    # ---- 图 ----
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei", "DejaVu Sans"]
    plt.rcParams["axes.unicode_minus"] = False
    fig, axes = plt.subplots(2, 3, figsize=(15, 11))
    for j, a in enumerate(A_GRID):
        ax = axes[j // 3][j % 3]
        for tag, mk, c in (("zeta", "o", "tab:blue"), ("L", "s", "tab:red")):
            pts = fit_data[(tag, a)]
            lts = np.array([p[0] for p in pts]); Ds = np.array([p[1] for p in pts])
            ax.scatter(np.exp(lts), Ds, marker=mk, c=c, label=tag, zorder=3)
            for law, xf, st in (("1_over_sqrtlogT", lambda t: 1.0 / np.sqrt(t), "--"),
                                ("1_over_logT", lambda t: 1.0 / t, ":")):
                x = xf(lts); k, b = np.polyfit(x, Ds, 1)
                ts = np.linspace(np.exp(lts.min()), np.exp(lts.max()), 60)
                ax.plot(ts, k * xf(np.log(ts)) + b, st, color=c, alpha=0.7,
                        label=tag + " " + law if False else None)
        ax.set_xscale("log"); ax.set_yscale("symlog", linthresh=1e-3)
        ax.set_title("a=" + a + "  Δ=A-GUE2 跨 T 衰减")
        ax.grid(alpha=0.3)
        ax.legend()
    fig.suptitle("S2(ii) 跨 T 衰减律判别：1/√logT（虚线） vs 1/logT（点线）", fontsize=13)
    fig.tight_layout(rect=[0, 0, 1, 0.96])
    fig.savefig(FIG, dpi=150)
    print("fig:", FIG)


if __name__ == "__main__":
    main()
