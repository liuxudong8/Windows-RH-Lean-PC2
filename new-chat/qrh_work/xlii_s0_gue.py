# -*- coding: utf-8 -*-
"""S0 判定收尾：有限 N GUE 模拟对照。
问题：实测 A(λ) vs GUE2 理论存在系统性负偏差平台（ζ ~−0.02 宽端）。
检验：有限 N GUE 特征值（同局部归一化流程）是否重现该平台。
- 若 GUE 模拟也给出 ≈−0.02 → 平台是有限 N/离散化伪影，实测与 GUE 完全一致；
- 若 GUE 模拟≈0 → 平台是真实信号（超 GUE 排斥）。
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

def gue2_a(a, R=60.0):
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    return 1.0 + 2.0 * float(np.trapezoid((1.0 - sinc(np.pi * u) ** 2) * sinc(np.pi * u / a) ** 4, u))

def pair_hist_const(z, rho_fn, half, binw):
    """u=Δ·ρ(x_mid)，rho_fn 逐点（GUE 半圆密度或常数）。"""
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

def A_from_hist(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n

def main():
    t0 = time.time()
    NMAT = 4000
    R = 12
    AGRID = [0.5, 1.0, 2.0, 4.0, 8.0]
    acc = {a: [] for a in AGRID}
    dens_acc = []
    rng = np.random.default_rng(2026)
    for r in range(R):
        # GUE 矩阵（谱宽校准后局部归一化）
        A = rng.normal(0.0, 1.0, (NMAT, NMAT))
        B = rng.normal(0.0, 1.0, (NMAT, NMAT))
        M = (A + 1j * B)
        M = (M + M.conj().T) / (2 * np.sqrt(NMAT))
        ev = np.sort(np.linalg.eigvalsh(M).real)
        sel = ev[(ev >= -0.6) & (ev <= 0.6)]
        if len(sel) < 200:
            continue
        rho_half = lambda x: (2.0 * NMAT / np.pi) * np.sqrt(np.maximum(0.0, 1.0 - np.asarray(x) ** 2))
        # 密度校准：先测最近邻均值，因子 1/nn_mean 使 s 平均=1
        dnn0 = np.diff(sel); dnn0 = dnn0[dnn0 > 0]
        tm0 = 0.5 * (sel[:-1] + sel[1:])
        nn0 = float(np.mean(dnn0 * rho_half(tm0)))
        cal = 1.0 / max(nn0, 1e-9)
        rho_cal = lambda x: rho_half(x) * cal
        uc, hist, n = pair_hist_const(sel, rho_cal, 40.0, 0.02)
        for a in AGRID:
            acc[a].append(A_from_hist(hist, uc, n, a))
        dnn = np.diff(sel)
        tm = 0.5 * (sel[:-1] + sel[1:])
        s = dnn * rho_cal(tm)
        dens_acc.append(float(np.mean(s)))
    res = {}
    for a in AGRID:
        v = np.array(acc[a])
        res[str(a)] = {"mean": float(v.mean()), "std": float(v.std()),
                       "dev_vs_GUE2": float(v.mean() - gue2_a(a))}
    print("GUE 模拟（N=%d×R=%d）：nn_mean_avg=%.4f" % (NMAT, R, np.mean(dens_acc)))
    print("%-6s %-10s %-10s %-10s %-10s" % ("a", "A_sim", "GUE2理论", "偏差", "实测ζ"))
    import json as _j
    real = _j.load(open(OUTDIR + r"\xlii_s0_v3.json", encoding="utf-8"))
    for a in AGRID:
        s = str(a)
        print("%-6.1f %-10.5f %-10.5f %-10.5f %-10.5f" % (a, res[s]["mean"], gue2_a(a),
                                                           res[s]["dev_vs_GUE2"], real["A_zeta"][s]))
    with open(OUTDIR + r"\xlii_s0_gue_sim.json", "w", encoding="utf-8") as f:
        json.dump({"N": NMAT, "R": R, "nn_mean_avg": float(np.mean(dens_acc)),
                   "A": {k: {"mean": v["mean"], "std": v["std"]} for k, v in res.items()},
                   "dev_vs_GUE2": {k: v["dev_vs_GUE2"] for k, v in res.items()},
                   "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    print("saved xlii_s0_gue_sim.json  elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
