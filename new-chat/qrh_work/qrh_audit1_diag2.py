# -*- coding: utf-8 -*-
"""QRH 数值定向 #1 诊断 2：L 根是否在 ζ 根附近聚集 + 并集序列模式。
检验：
(i) 每 ζ 零点附近 [γ-0.3, γ+0.3] 内的 L 根数均值 vs 均匀预期（rho_L*0.6≈1.15）；
(ii) 每 L 零点附近 [γ'-0.3, γ'+0.3] 内的 ζ 根数均值 vs 均匀预期（rho_z*0.6≈1.03）；
(iii) 并集（ζ+L 合并）相邻零点换族频率——若两族交替出现则 ~100% 换族；独立泊松则按密度比；
(iv) 若强聚集：距离相关函数 g(r)（跨族两点相关：L 根在 ζ 根距离 r 处的条件密度/均匀密度）。"""
import numpy as np

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
T = 6.0e5

def rho_zeta(t):
    return np.log(t / (2.0 * np.pi)) / (2.0 * np.pi)

def rho_L(t):
    return (np.log(t / (2.0 * np.pi)) + np.log(5.0) - 1.0) / (2.0 * np.pi)

def main():
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[z <= T]; l = l[l <= T]
    nz, nl = len(z), len(l)
    # (i) ζ 零点附近 0.3 区间内 L 根数
    lo_z = np.searchsorted(l, z - 0.3, side="left")
    hi_z = np.searchsorted(l, z + 0.3, side="left")
    cnt_zl = hi_z - lo_z
    exp_zl = rho_L(z) * 0.6
    print("每 ζ 零点 0.6 区间内 L 根数：mean=%.3f  均匀预期=%.3f  比值=%.2f" %
          (cnt_zl.mean(), exp_zl.mean(), cnt_zl.mean() / exp_zl.mean()))
    # (ii) L 零点附近 0.3 内 ζ 根数
    lo_l = np.searchsorted(z, l - 0.3, side="left")
    hi_l = np.searchsorted(z, l + 0.3, side="left")
    cnt_lz = hi_l - lo_l
    exp_lz = rho_zeta(l) * 0.6
    print("每 L 零点 0.6 区间内 ζ 根数：mean=%.3f  均匀预期=%.3f  比值=%.2f" %
          (cnt_lz.mean(), exp_lz.mean(), cnt_lz.mean() / exp_lz.mean()))
    # (iii) 并集序列模式
    allz = np.concatenate([np.stack([z, np.zeros(nz)], 1), np.stack([l, np.ones(nl)], 1)])
    allz = allz[np.argsort(allz[:, 0])]
    kind = allz[:, 1]
    flips = np.sum(kind[1:] != kind[:-1])
    print("并集相邻换族频率：%.4f  （ζ,L 独立时预期：%.4f；完全交替=1.0）" %
          (flips / (len(kind) - 1), 2.0 * (nz / (nz + nl)) * (nl / (nz + nl))))
    # 同族相邻频率（ζ,ζ 或 L,L）
    same = np.sum(kind[1:] == kind[:-1])
    print("同族相邻频率：%.4f" % (same / (len(kind) - 1)))
    # (iv) 跨族两点相关 g(r)：r∈[0.02,1.0] 分箱，L 根在 ζ 根距离 r 处条件密度 / 均匀密度
    bins = np.linspace(0.0, 1.0, 51)
    g = np.zeros(50); counts = np.zeros(50)
    mid = 0.5 * (bins[:-1] + bins[1:])
    # 对每个 ζ 零点，统计 L 根在 [γ+r, γ+r+dr]
    # 向量化：用 searchsorted 在 l 上查窗口
    for k in range(50):
        r0, r1 = bins[k], bins[k + 1]
        a = np.searchsorted(l, z + r0, side="left")
        b = np.searchsorted(l, z + r1, side="left")
        cnt = (b - a).sum()
        vol = (r1 - r0) * nz
        expected = vol * np.mean(rho_L(z))
        g[k] = cnt / expected if expected > 0 else float("nan")
    print("g(r) 跨族两点相关（r 分箱，每 5 箱打一行）：")
    for k in range(0, 50, 5):
        print("  r=[%.2f,%.2f]  g=%.3f" % (bins[k], bins[k + 5], float(np.nanmean(g[k:k + 5]))))

if __name__ == "__main__":
    main()
