# -*- coding: utf-8 -*-
"""骨头 2（N2）数值定向：ε–λ 联动——正则化 ε 对有效核宽的撑宽效应。
模型：K_{a,ε}(u) = sinc(πu/(a+2ε))²（正则化使有效核宽 a_eff = a+2ε）。
验证：(i) ε≤a（联动约束）时 A(K_{a,ε})−1 ≈ 0.16a³ 不被破坏；
      (ii) ε≫a 时 A−1 被 ε 撑大 → ~0.16(a+2ε)³。
GUE 直方图一次，所有 (a,ε) 档共用。
"""
import os, json, time
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"

def sinc(x):
    with np.errstate(divide="ignore", invalid="ignore"):
        x = np.asarray(x, dtype=float)
        return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def K_fejer(u, w):
    return sinc(np.pi * u / w) ** 2

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
    AG = [0.5, 0.25, 0.125, 0.06]
    ETA = [0.0, 0.1, 0.5, 1.0, 2.0, 5.0]   # eta = ε/a
    res = {str(a): {} for a in AG}
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
        for a in AG:
            for eta in ETA:
                w = a + 2.0 * eta * a
                A_ = 1.0 + float(np.sum(hist * K_fejer(uc, w) ** 2)) / n
                res[str(a)][str(eta)] = res[str(a)].get(str(eta), []) + [A_]
    out = {}
    print("%-7s %-7s %-12s %-12s %-12s" % ("a", "eta", "A_mean", "A-1", "0.16*a3_ref"))
    for a in AG:
        for eta in ETA:
            v = np.array(res[str(a)][str(eta)])
            m = float(v.mean()); s = float(v.std())
            ref = 0.16 * (a + 2.0 * eta * a) ** 3
            out.setdefault(str(a), {})[str(eta)] = {"mean": m, "std": s}
            print("%-7.3f %-7.2f %-12.6f %-12.2e %-12.2e" % (a, eta, m, m - 1.0, ref))
    with open(OUTDIR + r"\xlii_s7f_bone2.json", "w", encoding="utf-8") as f:
        json.dump({"N": NMAT, "R": R, "kernel": "fejer_effwidth", "A": out,
                   "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    # 图：A-1 vs eta（多 a 曲线），半对数
    fig, ax = plt.subplots(figsize=(7, 4.8))
    plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei", "DejaVu Sans"]
    plt.rcParams["axes.unicode_minus"] = False
    for a in AG:
        xs = []; ys = []
        for eta in ETA:
            v = np.array(res[str(a)][str(eta)])
            xs.append(eta); ys.append(float(v.mean()) - 1.0)
        ax.semilogy(xs, np.maximum(ys, 1e-12), "o-", lw=1.5, ms=4.5,
                    label=("a=%.3f" % a))
    ax.set_xlabel("eta = eps/a（正则化相对强度，对数线性）")
    ax.set_ylabel("A(K_{a,eps})-1（对数轴）")
    ax.set_title("骨头 2：epsilon-lambda 联动——eps 撑宽效应（eps/a 大时 A-1 被抬升）")
    ax.legend(fontsize=9)
    ax.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    out = os.path.join(OUTDIR, "xlii_s7f_bone2_fig.png")
    plt.savefig(out, dpi=200)
    print("saved", out, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
