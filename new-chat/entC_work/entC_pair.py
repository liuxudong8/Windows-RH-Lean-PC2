# -*- coding: utf-8 -*-
"""
entC_pair.py — 攻防 XXXIV 数值件 C1：二阶口径（配对和的离线 delta^2*lam^2 签名）
================================================================
机制：定理 3.1' 配对和 Σ_{γ≠γ'} f̂(i(ρ−ρ')λ/2π)，核依赖完整差 ρ−ρ'（含实部差）。
检验函数 f(x)=cos²(πx)·1_{|x|<1/2}，f̂(z)=(1/2)sinc(z)+(1/4)[sinc(z−1)+sinc(z+1)]。
在线（全临界线）核 f̂(iλΔγ/2π) 纯实（f 实偶）；离线零点 ρ=1/2−δ+iγ ⟹
核变 f̂(λ(−δ+iΔγ)/2π)，实部口径下一阶项（∝δλ·Re f̂'|_{x=0}=0，偶性）消失，
最低阶签名 = δ²λ² 级二阶量。

本脚本：
  C1a 场景 a（全在线）配对和 + 分窗背景涨落
  C1b 注入网格 p×δ：ΔPair 实测 vs 理论标度（δ² 平方律、p 线性）
  C1c 检测限 σ=ΔPair/std_global；反推威胁级（p=0.1018）的可测深度 δ_min(3σ)
数据：zeros_T6e5.npz（zeta/L 键）。运行：Anaconda python（numpy）。
"""
import numpy as np
import json
import os
import time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "entC_pair.json")

T = 6e5
LAM = np.log(T)          # 13.30468
PI = np.pi
R_CUT = 2.5              # 核窗口 λΔγ/2π ∈ [0, R_CUT]
W = 2.0 * PI * R_CUT / LAM   # 虚部窗口 ≈ 1.18

def fsinc(z):
    """sinc(z)=sin(πz)/(πz)（复解析延拓）。"""
    z = np.asarray(z, dtype=np.complex128)
    out = np.empty(z.shape, dtype=np.complex128)
    nz = z != 0
    out[nz] = np.sin(np.pi * z[nz]) / (np.pi * z[nz])
    out[~nz] = 1.0 + 0.0j
    return out

def fhat(z):
    """f̂(z)，f(x)=cos²(πx)·1_{|x|<1/2}。"""
    return 0.5 * fsinc(z) + 0.25 * (fsinc(z - 1.0) + fsinc(z + 1.0))

def kernel_on(dg):
    """在线配对核 f̂(iλΔγ/2π)（纯实）。"""
    z = 1j * LAM * dg / (2.0 * PI)
    return np.real(fhat(z))

def kernel_off(dg, delta):
    """离线对核实部 Re[f̂(λ(−δ+iΔγ)/2π)]。"""
    z = LAM * (-delta + 1j * dg) / (2.0 * PI)
    return np.real(fhat(z))

def load():
    d = np.load(NPZ)
    zeta = np.sort(np.asarray(d["zeta"], dtype=np.float64))
    L = np.sort(np.asarray(d["L"], dtype=np.float64))
    return zeta, L

def build_pairs(g):
    """向量化构造窗口内 (i,j) 对：|g[j]-g[i]| < W, j>i。返回 i_idx, j_idx, dg。"""
    n = len(g)
    ends = np.searchsorted(g, g + W, side="right")
    counts = ends - np.arange(n) - 1
    total = int(counts.sum())
    starts = np.zeros(n, dtype=np.int64)
    np.cumsum(counts[:-1], out=starts[1:])
    i_idx = np.repeat(np.arange(n), counts)
    pos = np.arange(total, dtype=np.int64) - np.repeat(starts, counts)
    j_idx = i_idx + pos + 1
    dg = g[j_idx] - g[i_idx]
    return i_idx, j_idx, dg

def pair_sum(g, i_idx, j_idx, dg, off_idx=None, delta=0.0):
    """配对和 Σ Re[f̂(i(ρ−ρ')λ/2π)]。off-on 对 K_off(Δγ;δ)，off-off 对 K_off(Δγ;2δ)。"""
    base = kernel_on(dg).sum()
    if off_idx is None or len(off_idx) == 0:
        return float(base), 0.0
    off = np.zeros(len(g), dtype=bool)
    off[off_idx] = True
    oi = off[i_idx]
    oj = off[j_idx]
    m_off = oi | oj
    m_both = oi & oj
    if not m_off.any():
        return float(base), 0.0
    dg_m = dg[m_off]
    delta_eff = np.where(m_both[m_off], 2.0 * delta, delta)
    d = (kernel_off(dg_m, delta_eff) - kernel_on(dg_m)).sum()
    return float(base + d), float(d)

def main():
    t0 = time.time()
    zeta, L = load()
    res = {"T": T, "lam": float(LAM),
           "kernel": "fhat of f=cos^2(pi x) 1_{|x|<1/2}", "R_cut": R_CUT,
           "W": float(W), "seed": 20261023}
    rng = np.random.default_rng(20261023)

    per_family = {}
    for name, g in (("zeta", zeta), ("L", L)):
        n = len(g)
        t1 = time.time()
        i_idx, j_idx, dg = build_pairs(g)
        n_pairs = len(dg)
        n_win = 40
        edges = np.linspace(0, n, n_win + 1).astype(int)
        win_sums = []
        for w_i in range(n_win):
            a, b = edges[w_i], edges[w_i + 1]
            seg = g[a:b]
            if len(seg) < 2:
                win_sums.append(0.0); continue
            ii, jj, dd = build_pairs(seg)
            win_sums.append(float(kernel_on(dd).sum()))
        win_sums = np.array(win_sums)
        win_mean = float(win_sums.mean())
        win_std = float(win_sums.std(ddof=1)) if n_win > 1 else 0.0
        std_global = win_std * np.sqrt(n_win)
        pair_on = float(kernel_on(dg).sum())

        p_list = [0.001, 0.005, 0.01, 0.05, 0.1018]
        delta_list = [0.005, 0.01, 0.02, 0.05]
        grid = []
        for p in p_list:
            n_off = int(round(p * n))
            idx = rng.choice(n, size=n_off, replace=False)
            idx.sort()
            for delta in delta_list:
                _, d = pair_sum(g, i_idx, j_idx, dg, idx, delta)
                sigma = d / std_global if std_global > 0 else float("nan")
                grid.append({"p": p, "n_off": n_off, "delta": delta,
                             "delta_pair": float(d), "sigma": float(sigma)})
        scal = [x for x in grid if abs(x["p"] - 0.1018) < 1e-12]
        if scal:
            d2 = np.array([x["delta"] ** 2 for x in scal])
            dp = np.array([x["delta_pair"] for x in scal])
            A = d2.reshape(-1, 1)
            coef = float(np.linalg.lstsq(A, dp, rcond=None)[0][0])
        else:
            coef = float("nan")
        delta_min = None
        if scal:
            sigs = np.array([x["sigma"] for x in scal])
            ds = np.array([x["delta"] for x in scal])
            pos = np.where(sigs >= 3.0)[0]
            if len(pos):
                i0 = pos[0]
                if i0 == 0:
                    delta_min = float(ds[0])
                else:
                    s0, s1 = sigs[i0 - 1], sigs[i0]
                    d0, d1 = ds[i0 - 1], ds[i0]
                    delta_min = float(d0 + (3.0 - s0) * (d1 - d0) / (s1 - s0))
        # 理论 δ² 系数（每对，用实际距离分布）：Re f̂'' 在虚轴 → (λ/2π)²·Re f̂''(iy)/2
        K_on = kernel_on(dg)
        # 数值二阶：中心差分 f̂(x+iy) 在 x=0 的二阶实部
        dx = 1e-4
        z0 = 1j * LAM * dg / (2.0 * PI)
        fpp = (np.real(fhat(z0 + dx)) + np.real(fhat(z0 - dx)) - 2.0 * K_on) / (dx * dx)
        th_coef_per_pair = float((K_on * 0.0 + fpp * 0.5).mean())  # 每对 δ² 系数 ≈ fpp/2 平均
        per_family[name] = {
            "n": int(n), "n_pairs": int(n_pairs), "pair_on": pair_on,
            "win_mean": win_mean, "win_std": win_std, "std_global": std_global,
            "grid": grid,
            "delta2_coef_p1018": coef,
            "delta_min_3sigma_p1018": delta_min,
            "theory_delta2_coef_per_pair": th_coef_per_pair,
            "build_s": round(time.time() - t1, 1),
        }
        print(f"[{name}] n={n} pairs={n_pairs} pair_on={pair_on:.3e} "
              f"std_global={std_global:.3e} delta_min(3σ,p=0.1018)={delta_min} "
              f"coef_p1018={coef:.3e} th_coef={th_coef_per_pair:.3e}")

    res["per_family"] = per_family
    res["runtime_s"] = round(time.time() - t0, 1)
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(res, f, ensure_ascii=False, indent=1)
    print("saved", OUT)

if __name__ == "__main__":
    main()
