# -*- coding: utf-8 -*-
"""
entC_scan.py — 攻防 XXXIV C1b/C1c：跨族配对和 + 核窗口扫描
================================================================
C1b 跨族：配对和 Σ_{γζ,γL} Re[f̂(i(ρ_ζ−ρ_L)λ/2π)]——定理 3.1' 主场。
    注入：L 族 p% 零点离线（δ）——签名 = Σ_off对[K_off−K_on]。
C1c 窗口扫描：zeta 族 R_CUT ∈ {1.5,2.0,3.0}，威胁级 p=0.1018、δ=0.05——σ 变化。
核：f̂(z)=(1/2)sinc(z)+(1/4)[sinc(z−1)+sinc(z+1)]，f=cos²(πx)·1_{|x|<1/2}。
"""
import numpy as np
import json
import os
import time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "entC_scan.json")

LAM = np.log(6e5)
PI = np.pi

def fsinc(z):
    z = np.asarray(z, dtype=np.complex128)
    out = np.empty(z.shape, dtype=np.complex128)
    nz = z != 0
    out[nz] = np.sin(np.pi * z[nz]) / (np.pi * z[nz])
    out[~nz] = 1.0 + 0.0j
    return out

def fhat(z):
    return 0.5 * fsinc(z) + 0.25 * (fsinc(z - 1.0) + fsinc(z + 1.0))

def k_on(dg):
    return np.real(fhat(1j * LAM * dg / (2.0 * PI)))

def k_off(dg, delta):
    return np.real(fhat(LAM * (-delta + 1j * dg) / (2.0 * PI)))

def build_pairs(g, W):
    n = len(g)
    ends = np.searchsorted(g, g + W, side="right")
    counts = ends - np.arange(n) - 1
    total = int(counts.sum())
    starts = np.zeros(n, dtype=np.int64)
    np.cumsum(counts[:-1], out=starts[1:])
    i_idx = np.repeat(np.arange(n), counts)
    pos = np.arange(total, dtype=np.int64) - np.repeat(starts, counts)
    j_idx = i_idx + pos + 1
    return i_idx, j_idx, g[j_idx] - g[i_idx]

def build_cross(gA, gB, W):
    """跨族对：A 每点窗口内 B 的点。返回 (iA, jB, dg)。"""
    nA = len(gA)
    ends = np.searchsorted(gB, gA + W, side="right")
    starts = np.searchsorted(gB, gA - W, side="left")
    counts = ends - starts
    total = int(counts.sum())
    s2 = np.zeros(nA, dtype=np.int64)
    np.cumsum(counts[:-1], out=s2[1:])
    iA = np.repeat(np.arange(nA), counts)
    pos = np.arange(total, dtype=np.int64) - np.repeat(s2, counts)
    jB = starts[iA] + pos
    return iA, jB, gB[jB] - gA[iA]

def main():
    t0 = time.time()
    d = np.load(NPZ)
    zeta = np.sort(np.asarray(d["zeta"], dtype=np.float64))
    L = np.sort(np.asarray(d["L"], dtype=np.float64))
    rng = np.random.default_rng(20261023)
    res = {"lam": float(LAM), "kernel": "fhat cos^2", "seed": 20261023}

    # ---- C1b 跨族（R=2.5）----
    R = 2.5
    W = 2.0 * PI * R / LAM
    iA, jB, dg = build_cross(zeta, L, W)
    K = k_on(dg)
    pair_on = float(K.sum())
    n_pairs = len(dg)
    # 分窗背景：按 ζ 序 40 窗（窗内跨族对）
    n_win = 40
    edges = np.linspace(0, len(zeta), n_win + 1).astype(int)
    win = []
    for w_i in range(n_win):
        a, b = edges[w_i], edges[w_i + 1]
        seg = zeta[a:b]
        i2, j2, dd = build_cross(seg, L, W)
        win.append(float(k_on(dd).sum()))
    win = np.array(win)
    std_global = float(win.std(ddof=1) * np.sqrt(n_win))
    # 注入：L 族 p% 离线
    cross = {"n_pairs": int(n_pairs), "pair_on": pair_on, "std_global": std_global, "grid": []}
    for p in [0.01, 0.05, 0.1018]:
        n_off = int(round(p * len(L)))
        idx = np.sort(rng.choice(len(L), size=n_off, replace=False))
        offB = np.zeros(len(L), dtype=bool)
        offB[idx] = True
        m = offB[jB]
        dg_m = dg[m]
        dval = float((k_off(dg_m, 0.05) - k_on(dg_m)).sum())
        cross["grid"].append({"p": p, "n_off": n_off, "delta": 0.05,
                              "delta_pair": dval, "sigma": dval / std_global})
    res["cross_family"] = cross
    print("[cross] pairs=%d pair_on=%.3e std_global=%.3e" % (n_pairs, pair_on, std_global))
    for g in cross["grid"]:
        print("   p=%.4f sigma=%.3f delta_pair=%.1f" % (g["p"], g["sigma"], g["delta_pair"]))

    # ---- C1c 窗口扫描（zeta 族威胁级 δ=0.05）----
    res["window_scan"] = []
    for R in [1.5, 2.0, 3.0]:
        W = 2.0 * PI * R / LAM
        ii, jj, dg2 = build_pairs(zeta, W)
        K2 = k_on(dg2)
        pair_on2 = float(K2.sum())
        n_win = 40
        edges = np.linspace(0, len(zeta), n_win + 1).astype(int)
        win = []
        for w_i in range(n_win):
            a, b = edges[w_i], edges[w_i + 1]
            seg = zeta[a:b]
            i3, j3, dd = build_pairs(seg, W)
            win.append(float(k_on(dd).sum()))
        win = np.array(win)
        std_g = float(win.std(ddof=1) * np.sqrt(n_win))
        p = 0.1018
        n_off = int(round(p * len(zeta)))
        idx = np.sort(rng.choice(len(zeta), size=n_off, replace=False))
        off = np.zeros(len(zeta), dtype=bool)
        off[idx] = True
        oi, oj = off[ii], off[jj]
        m = oi | oj
        mb = oi & oj
        dg_m = dg2[m]
        de = np.where(mb[m], 2.0 * 0.05, 0.05)
        dval = float((k_off(dg_m, de) - k_on(dg_m)).sum())
        res["window_scan"].append({"R": R, "W": float(W), "n_pairs": int(len(dg2)),
                                   "pair_on": pair_on2, "std_global": std_g,
                                   "delta_pair_d05": dval, "sigma": dval / std_g})
        print("[win R=%.1f] pairs=%d pair_on=%.3e std_global=%.3e sigma(d=0.05)=%.3f"
              % (R, len(dg2), pair_on2, std_g, dval / std_g))

    res["runtime_s"] = round(time.time() - t0, 1)
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(res, f, ensure_ascii=False, indent=1)
    print("saved", OUT)

if __name__ == "__main__":
    main()
