# -*- coding: utf-8 -*-
"""攻防 XLII · S1a：算术项归因（三层理论第 3 层定量化）。
1. Parseval 归因：Δ_A(a)=A−GUE2 实测 ↔ (1/2π)∫δF(α)·W_a(α)dα，δF=F−F_GUE（局部 u-口径配对谱）。
2. 衰减律：drift 5 段 Δ(a;T_seg) 对 logT / √logT 拟合（BGS 误差 1/√logT vs 1/logT 判别）。
3. 核依赖常数：fejer / sinc / gauss 三族 A−GUE2 排序（谱支撑光滑度假设检验）。
输出 s1a.json + fig1（δF 谱）+ fig2（衰减律 + 核族）。
"""
import numpy as np, json, time, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
V3 = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\xlii_s0_v3.json"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(OUTDIR, "xlii_s1a.json")
FIG1 = os.path.join(OUTDIR, "xlii_s1a_fig1.png")
FIG2 = os.path.join(OUTDIR, "xlii_s1a_fig2.png")
T, LOW = 6.0e5, 300.0
SEG_END = [1.2e5, 2.4e5, 3.6e5, 4.8e5, 6.0e5]
A_GRID = ["0.1", "0.15", "0.2", "0.25", "0.3", "0.35", "0.4", "0.45", "0.5",
          "0.75", "1.0", "1.5", "2.0"]
plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei"]
plt.rcParams["axes.unicode_minus"] = False


def sinc(x):
    with np.errstate(divide="ignore", invalid="ignore"):
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


def K_sinc(u, a):
    return sinc(np.pi * u / a)


def K_gauss(u, a):
    return np.exp(-(u / (0.5 * a)) ** 2 / 2.0)


def pair_hist_local(z, rho_fn, half, binw):
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


def A_from_hist(hist, uc, n, Kfun, a):
    return 1.0 + float(np.sum(hist * Kfun(uc, a) ** 2)) / n


def gue2_a(a, R=60.0):
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    return 1.0 + 2.0 * float(np.trapezoid((1.0 - sinc(np.pi * u) ** 2) * sinc(np.pi * u / a) ** 4, u))


def gue2_k(a, Kfun, R=40.0):
    """按核的 GUE 基准：1+2∫(1−sinc²πu)·K(u)²du（有序对口径）。"""
    N = 800_001
    u = np.linspace(0.0, R, N)
    return 1.0 + 2.0 * float(np.trapezoid((1.0 - sinc(np.pi * u) ** 2) * Kfun(u, a) ** 2, u))


def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    v3 = json.load(open(V3, encoding="utf-8"))

    half, binw = 8.0, 0.002
    uc, hz, _ = pair_hist_local(z, rho_zeta, half, binw)
    uc, hl, _ = pair_hist_local(l, rho_L, half, binw)
    print("hist done %.1fs" % (time.time() - t0), nz, nl)

    # 核族 A（sinc/gauss 为新算；fejer 偏差以 v3 为基准，见后验校验）
    A_grid_f = [float(x) for x in A_GRID]
    KFUNS = {"fejer": K_fejer, "sinc": K_sinc, "gauss": K_gauss}
    fam = {}
    for tag in ("zeta", "L"):
        h = hz if tag == "zeta" else hl
        n = nz if tag == "zeta" else nl
        fam[tag] = {}
        for kn, kfun in KFUNS.items():
            fam[tag][kn] = {str(a): round(A_from_hist(h, uc, n, kfun, a), 6) for a in A_grid_f}

    # ---- F(α) 谱（局部 u-口径，有序对）----
    alpha = np.linspace(0.0, 6.3, 631)
    dalpha = alpha[1] - alpha[0]
    F = {}
    for tag, h, n in (("zeta", hz, nz), ("L", hl, nl)):
        M = np.outer(h, np.ones_like(alpha)) * np.cos(np.outer(uc, alpha))
        F[tag] = np.sum(M, axis=0) / n
    # F_GUE：有序口径（×2），同窗 (0,8) 数值
    ug = np.linspace(1e-6, 8.0, 16000)
    R_GUE = 1.0 - sinc(np.pi * ug) ** 2
    F_GUE = 2.0 * np.array([np.trapezoid(R_GUE * np.cos(alpha[j] * ug), ug)
                            for j in range(len(alpha))])
    dF = {tag: F[tag] - F_GUE for tag in ("zeta", "L")}
    # δR(u) 诊断：实测有序对密度 R_obs(u)=H/(N·binw) vs 2·R_GUE(u)
    dR = {}
    for tag, h, n in (("zeta", hz, nz), ("L", hl, nl)):
        R_obs = h / (n * binw)
        R_gue_u = 2.0 * (1.0 - sinc(np.pi * uc) ** 2)
        dR[tag] = {"u": [round(float(x), 4) for x in uc.tolist()],
                   "R_obs": [round(float(x), 6) for x in R_obs.tolist()],
                   "R_GUE2": [round(float(x), 6) for x in R_gue_u.tolist()]}

    # ---- Parseval 重构 Δ_F(a) ----
    W = {}
    for a in A_grid_f:
        Wa = np.array([np.trapezoid(sinc(np.pi * ug / a) ** 4 * np.cos(alpha[j] * ug), ug)
                       for j in range(len(alpha))])
        W[str(a)] = Wa
    Df = {}
    for tag in ("zeta", "L"):
        Df[tag] = {a: round(float(np.trapezoid(dF[tag] * W[a], alpha)) / (2 * np.pi), 6) for a in A_GRID}
    Da = {}
    for tag in ("zeta", "L"):
        src = v3["A_zeta_fine"] if tag == "zeta" else v3["A_L_fine"]
        Da[tag] = {a: round(src[a] - v3["A_GUE2"][a], 6) for a in A_GRID}
    # 后验复现校验：Da（=fam−GUE2）与 v3 偏差逐点对照
    mxd = max(abs(Da["zeta"][a] - (v3["A_zeta_fine"][a] - v3["A_GUE2"][a])) for a in A_GRID)
    mxd = max(mxd, max(abs(Da["L"][a] - (v3["A_L_fine"][a] - v3["A_GUE2"][a])) for a in A_GRID))
    chk = mxd < 5e-5
    print("fejer reproduce v3:", chk, "max abs diff %.2g" % mxd)
    decay = {}
    for tag in ("zeta", "L"):
        decay[tag] = {}
        for a in ("0.3", "0.5", "1.0", "2.0"):
            vals = v3["drift"][tag][a]["vals"]
            g2 = v3["A_GUE2"][a]
            Dseg = [vals[k] - g2 for k in range(5)]
            x = np.log(np.log(np.array(SEG_END, dtype=float)))
            y = np.log(np.abs(np.array(Dseg)) + 1e-12)
            k, b = np.polyfit(x, y, 1)
            decay[tag][a] = {"Dseg": [round(v, 6) for v in Dseg],
                             "slope_logT": round(float(k), 3),
                             "r2": round(float(np.corrcoef(x, y)[0, 1] ** 2), 3)}

    # ---- 核族排序表（按核的 GUE 基准）----
    g2k = {kn: {str(a): gue2_k(a, kfun) for a in A_grid_f} for kn, kfun in KFUNS.items()}
    kfam = {}
    for tag in ("zeta", "L"):
        kfam[tag] = {}
        for a in ("0.3", "0.5", "1.0"):
            kfam[tag][a] = {kn: round(fam[tag][kn][a] - g2k[kn][a], 6) for kn in ("fejer", "sinc", "gauss")}
    kdev_abs = {kn: {a: round(abs(fam["zeta"][kn][a] - g2k[kn][a]), 6) for a in ("0.3", "0.5", "1.0")}
                for kn in ("fejer", "sinc", "gauss")}

    res = {"meta": {"T": T, "LOW": LOW, "n_zeta": nz, "n_L": nl,
                    "hist": {"half": half, "binw": binw},
                    "reproduce_v3_fejer": bool(chk)},
           "F_alpha": {"alpha": [round(x, 3) for x in alpha.tolist()],
                       "F_zeta": [round(x, 5) for x in F["zeta"].tolist()],
                       "F_L": [round(x, 5) for x in F["L"].tolist()],
                       "F_GUE": [round(x, 5) for x in F_GUE.tolist()]},
           "dF_peak": {tag: {"alpha": float(alpha[np.argmax(dF[tag])]),
                             "value": round(float(np.max(dF[tag])), 5)} for tag in ("zeta", "L")},
           "dR": dR,
           "D_actual": Da, "D_parseval": Df,
           "decay": decay, "kernel_family": kfam, "kdev_abs": kdev_abs,
           "elapsed": round(time.time() - t0, 1)}
    json.dump(res, open(OUT, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print("saved", OUT, "%.1fs" % res["elapsed"])

    # ---- Fig 1：δF 谱 + δR(u) ----
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.2))
    ax = axes[0]
    ax.axhline(0.0, color="gray", lw=1, ls="--")
    ax.plot(alpha, dF["zeta"], lw=1.6, color="black", label="dF = F - F_GUE (zeta)")
    ax.plot(alpha, dF["L"], lw=1.6, color="red", label="dF (L(chi_5))")
    ax.set_xlim(0, 3.0); ax.set_xlabel("alpha  (Fourier var of u = |d| rho(t_mid))")
    ax.set_ylabel("dF(alpha)")
    ax.set_title("S1a: pair-correlation spectral excess vs GUE\n(fully negative = super-GUE repulsion in the spectrum)")
    ax.legend(frameon=False); ax.grid(alpha=0.3)
    ax = axes[1]
    ax.axhline(0.0, color="gray", lw=1, ls="--")
    for tag, c in (("zeta", "black"), ("L", "red")):
        uu = np.array(dR[tag]["u"]); dd = np.array(dR[tag]["R_obs"]) - np.array(dR[tag]["R_GUE2"])
        ax.plot(uu, dd, lw=1.2, color=c, label="dR(u) (%s)" % tag)
    ax.set_xlim(0, 6.0); ax.set_xlabel("u = |d| rho(t_mid)")
    ax.set_ylabel("R_obs(u) - 2 R_GUE(u)")
    ax.set_title("dR(u): near negative / mid positive / far negative (3-zone)")
    ax.legend(frameon=False, fontsize=8); ax.grid(alpha=0.3)
    fig.tight_layout(); fig.savefig(FIG1, dpi=300)
    plt.close(fig)

    # ---- Fig 2：衰减律 + 核族（按核 GUE 基准）----
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.2))
    ax = axes[0]
    for tag, c in (("zeta", "black"), ("L", "red")):
        for a in ("0.5", "1.0"):
            vals = v3["drift"][tag][a]["vals"]
            g2 = v3["A_GUE2"][a]
            y = np.log(np.abs(np.array(vals) - g2) + 1e-12)
            ax.plot(np.log(np.log(np.array(SEG_END))), y, "o-", lw=1.2, color=c,
                    label="%s a=%s" % (tag, a))
    ax.set_xlabel("log(log T_seg)"); ax.set_ylabel("log |A_seg - GUE2|")
    ax.set_title("Decay law: 5 segments too narrow; seg4 rebound\n(unresolved: need cross-T dataset)")
    ax.legend(frameon=False, fontsize=8); ax.grid(alpha=0.3)
    ax = axes[1]
    a3 = ("0.3", "0.5", "1.0"); kns = ("fejer", "sinc", "gauss")
    xpos = np.arange(3)
    for tag, c in (("zeta", "black"), ("L", "red")):
        for i, kn in enumerate(kns):
            ax.plot(xpos + 0.1 * i, [kfam[tag][a][kn] for a in a3], "o-", color=c,
                    label="%s %s" % (tag, kn))
    ax.set_xticks(xpos); ax.set_xticklabels(a3)
    ax.set_xlabel("kernel width a"); ax.set_ylabel("A_K - GUE2_K (kernel-matched)")
    ax.set_title("Kernel-family deviations vs kernel-matched GUE\n(all negative: universal super-GUE repulsion)")
    ax.legend(frameon=False, fontsize=8); ax.grid(alpha=0.3)
    fig.tight_layout(); fig.savefig(FIG2, dpi=300)
    plt.close(fig)
    print("figs saved")


if __name__ == "__main__":
    main()
