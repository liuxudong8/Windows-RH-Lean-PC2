# -*- coding: utf-8 -*-
"""骨头 1（N1）数值定向：超支撑配对常数 A(K_a) → 1 当核宽 a → 0。
理论（BGS 引理 5 缩放不变性 + 偶核）：A(K_a) = 1 + Σ_{Δ≠0} K̂_a(δΔ)²/N → 1
（a→0 时 K̂_a 在非零频率处衰减，平方和消失）。
复用 S0 GUE 管线（xlii_s0_gue.py 同口径：局部归一化 + Fejer 核），扫小 a。
"""
import numpy as np, time, json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"

def sinc(x):
    with np.errstate(divide="ignore", invalid="ignore"):
        x = np.asarray(x, dtype=float)
        return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2

def pair_hist_const(z, rho_fn, half, binw):
    n = len(z)
    nb = int(np.ceil(half / binw)) + 1
    hist = np.zeros(nb)
    win_raw = half / 0.5
    chunk = 100000
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

def main():
    t0 = time.time()
    NMAT = 4000
    R = 12
    AGRID = [0.5, 0.25, 0.125, 0.06, 0.03, 0.015, 0.008]
    acc = {a: [] for a in AGRID}
    rng = np.random.default_rng(2026)
    for r in range(R):
        A = rng.normal(0.0, 1.0, (NMAT, NMAT))
        B = rng.normal(0.0, 1.0, (NMAT, NMAT))
        M = (A + 1j * B)
        M = (M + M.conj().T) / (2 * np.sqrt(NMAT))
        ev = np.sort(np.linalg.eigvalsh(M).real)
        sel = ev[(ev >= -0.6) & (ev <= 0.6)]
        if len(sel) < 200:
            continue
        rho_half = lambda x: (2.0 * NMAT / np.pi) * np.sqrt(np.maximum(0.0, 1.0 - np.asarray(x) ** 2))
        dnn0 = np.diff(sel); dnn0 = dnn0[dnn0 > 0]
        tm0 = 0.5 * (sel[:-1] + sel[1:])
        nn0 = float(np.mean(dnn0 * rho_half(tm0)))
        cal = 1.0 / max(nn0, 1e-9)
        rho_cal = lambda x: rho_half(x) * cal
        uc, hist, n = pair_hist_const(sel, rho_cal, 40.0, 0.02)
        for a in AGRID:
            A_ = 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n
            acc[a].append(A_)
    res = {}
    for a in AGRID:
        v = np.array(acc[a])
        res[str(a)] = {"mean": float(v.mean()), "std": float(v.std()),
                       "dev_1": float(v.mean() - 1.0)}
    print("%-8s %-12s %-10s %-14s" % ("a", "A_mean", "A_std", "A-1"))
    for a in AGRID:
        r_ = res[str(a)]
        print("%-8.3f %-12.6f %-10.6f %-14.2e" % (a, r_["mean"], r_["std"], r_["dev_1"]))
    with open(OUTDIR + r"\xlii_s7f_bone1.json", "w", encoding="utf-8") as f:
        json.dump({"N": NMAT, "R": R, "kernel": "fejer", "A": res,
                   "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    # 图：A-1 随 a（log-log）
    aa = np.array(AGRID, dtype=float)
    dev = np.array([res[str(a)]["dev_1"] for a in AGRID], dtype=float)
    fig, ax = plt.subplots(figsize=(7, 4.6))
    plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei", "DejaVu Sans"]
    plt.rcParams["axes.unicode_minus"] = False
    ax.loglog(aa, np.maximum(dev, 1e-12), "o-", color="#C0392B", lw=1.6, ms=5,
              label="A(K_a)-1（GUE 实测）")
    ax.loglog(aa, 1.0 * aa, "--", color="#7F8C8D", lw=1.1, label="~a（线性参考）")
    ax.set_xlabel("核宽 a（对数轴）")
    ax.set_ylabel("A(K_a)-1（对数轴）")
    ax.set_title("骨头 1：超支撑配对常数 A(K_a)→1（a→0）")
    ax.legend(fontsize=9)
    ax.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    out = os.path.join(OUTDIR, "xlii_s7f_bone1_fig.png")
    plt.savefig(out, dpi=200)
    print("saved", out, "elapsed %.1fs" % (time.time() - t0))

import os
if __name__ == "__main__":
    main()
