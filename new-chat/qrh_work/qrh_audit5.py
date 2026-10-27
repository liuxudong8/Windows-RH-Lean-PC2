# -*- coding: utf-8 -*-
"""QRH 常数机制攻坚 · 数值定向 #5：并集配对和系数 A 的核族扫描（变分常数数值构造）。
Lamzouri Proposition 2.1：N₀ˢ/N ≥ 2 − A，A = Σ_{z,s∈Z} K(z−s)² / Σ1，K=η²^、K(0)=1。
- 无条件单族：A_MT=C_MT=1.3275（最优核）→ 0.6725
- 7/8 门槛：A ≤ 1.125（0.875=2−1.125）
本件实测并集 Z_K=Z_ζ∪Z_L 的 A（核族扫描）：
(i) A_ζ（ζ 族内）、A_L（L 族内）、A_cross（跨族）、A_union（并集总）；
(ii) 加权预测 A_union^pred=(N_ζ A_ζ + N_L A_L + 2 N_cross A_cross)/N_K 类口径 vs 实测；
(iii) 判定：实测最小 A 离 1.125 多远——拟随机（GUE）前提下 7/8 的数值现实性。
核族：K(u)=sinc(πu)（η=矩形）；K(u)=sinc(πu)²（Fejér，η=三角）；K(u)=e^{-u²/2}（高斯）。
配对尺度 δ=logT/(2π)，截断 R=8。输出 qrh_audit5.json。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\qrh_audit5.json"
T = 6.0e5
LOW = 300.0
R = 8.0

def K_sinc(u):
    u = np.asarray(u, dtype=float)
    x = np.pi * u
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def K_fejer(u):
    x = np.pi * u
    return np.where(np.abs(x) < 1e-12, 1.0, (np.sin(x) / x) ** 2)

def K_gauss(u):
    return np.exp(-u * u / 2.0)

def pair_sum_A(zeros, rho, delta, Kfun, label):
    """A = Σ K(δ·|γ-γ'|)² / n。窗口截断 |γ-γ'| ≤ R/δ（每零点直算窗口内邻居）。"""
    z = np.asarray(zeros, dtype=float)
    n = len(z)
    if n == 0:
        return float("nan")
    half = R / delta
    lo = np.searchsorted(z, z - half, side="left")
    hi = np.searchsorted(z, z + half, side="right")
    tot = 0.0
    for i in range(n):
        seg = z[lo[i]:hi[i]]
        if seg.size == 0:
            continue
        dd = delta * np.abs(seg - z[i])
        tot += float(np.sum(Kfun(dd) ** 2))
    return tot / n

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    N_K = nz + nl
    delta = np.log(T) / (2.0 * np.pi)
    print("T=%.0f  nz=%d nl=%d N_K=%d  δ=%.4f  R=%.0f" % (T, nz, nl, N_K, delta, R))
    # 并集排序数组（用于跨族窗口）
    zz = np.stack([z, np.zeros(nz)], 1); ll = np.stack([l, np.ones(nl)], 1)
    allz = np.concatenate([zz, ll]); allz = allz[np.argsort(allz[:, 0])]
    tt = allz[:, 0]; kind = allz[:, 1]
    kernels = [("sinc", K_sinc), ("fejer", K_fejer), ("gauss", K_gauss)]
    rows = []
    for name, kf in kernels:
        A_zeta = pair_sum_A(z, 0.0, delta, kf, "zeta")
        A_L = pair_sum_A(l, 0.0, delta, kf, "L")
        # 并集 A（全配对）
        A_union = pair_sum_A(tt, 0.0, delta, kf, "union")
        # 跨族 A：并集总 - 族内
        A_cross_raw = A_union * N_K - (A_zeta * nz + A_L * nl)
        # 跨族"每零点对"系数：跨族对总数 = nz*nl（近似）→ 每对平均 K²
        # 归一化口径：A_cross_per = 跨族ΣK² / N_K（与 A_union 同口径）
        A_cross_per_N = A_cross_raw / N_K
        row = {"kernel": name, "A_zeta": A_zeta, "A_L": A_L, "A_union": A_union,
               "A_cross_extra_per_N": A_cross_per_N}
        rows.append(row)
        print("%-6s  A_ζ=%.4f  A_L=%.4f  A_union=%.4f  A_cross_extra=%.4f"
              % (name, A_zeta, A_L, A_union, A_cross_per_N))
    ref = {"C_MT": 1.3274992963205, "C0": 0.6725007, "threshold_7over8_A": 1.125,
           "threshold_7over8_ratio": 0.875, "note": "A = ΣK²/Σ1；N₀ˢ/N ≥ 2−A（Proposition 2.1）"}
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"delta": delta, "R": R, "nz": nz, "nl": nl, "N_K": N_K,
                   "rows": rows, "reference": ref, "elapsed": time.time() - t0},
                  f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
