# -*- coding: utf-8 -*-
"""QRH 数值定向 #1 诊断：跨族间距异常的来源。
怀疑：L 零点数组混入 ζ 根（R-S 求根重叠）→ 跨族近重合 → mean 0.27。
检验：(i) 跨族未归一化间距 d 的分位数；(ii) d<1e-3 / <1e-2 / <1e-1 的对数；
(iii) 两族相同值（容差）计数；(iv) 每个 ζ 零点最近 L 间距的 T 分段统计（低/中/高段）。"""
import numpy as np, json

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
T = 6.0e5

def main():
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[z <= T]; l = l[l <= T]
    nz, nl = len(z), len(l)
    print("nz=%d nl=%d" % (nz, nl))
    # 跨族最近间距（未归一化）
    idx = np.searchsorted(l, z, side="right")
    idx = np.clip(idx, 1, len(l) - 1)
    dL = np.minimum(np.abs(l[idx] - z), np.abs(l[idx - 1] - z))
    # 分位数
    qs = [0.001, 0.01, 0.05, 0.1, 0.25, 0.5, 0.75, 0.9, 0.99]
    print("cross-spacing quantiles:", np.round(np.quantile(dL, qs), 6).tolist())
    for th in [1e-6, 1e-4, 1e-3, 1e-2, 0.05, 0.1, 0.2]:
        cnt = int(np.sum(dL < th))
        print("d<%-6g : %d (%.4f%%)" % (th, cnt, 100.0 * cnt / nz))
    # 两族相同值（容差）
    tol = 1e-6
    i = 0; j = 0; common = 0
    while i < nz and j < nl:
        if abs(z[i] - l[j]) < tol:
            common += 1; i += 1; j += 1
        elif z[i] < l[j]:
            i += 1
        else:
            j += 1
    print("common(tol=1e-6):", common)
    # T 分段：低（<1e5）中（1e5-3e5）高（3e5-6e5）
    for lo, hi in [(50, 1e5), (1e5, 3e5), (3e5, 6e5)]:
        m = (z >= lo) & (z < hi)
        if m.sum() == 0:
            continue
        dm = dL[m]
        med = np.median(dm)
        mean_u = dm.mean()
        # 并集平均间距参考：1/(rho_z+rho_L) at mid
        tmid = (lo + hi) / 2.0
        rho_z = np.log(tmid / (2.0 * np.pi)) / (2.0 * np.pi)
        rho_L = (np.log(tmid / (2.0 * np.pi)) + np.log(5.0) - 1.0) / (2.0 * np.pi)
        print("T in [%g,%g): n=%d  mean_d=%.4f  med_d=%.4f  并集期望间距=%.4f" %
              (lo, hi, m.sum(), mean_u, med, 1.0 / (rho_z + rho_L)))
    # 最近 L 间距的分布形状（粗分箱）
    hist, edges = np.histogram(dL, bins=30, range=(0.0, 1.0))
    print("hist dL [0,1] (30 bins):", hist.tolist())

if __name__ == "__main__":
    main()
