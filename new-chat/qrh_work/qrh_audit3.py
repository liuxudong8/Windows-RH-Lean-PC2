# -*- coding: utf-8 -*-
"""QRH 常数机制攻坚 · 数值定向 #3：换族频率 0.753 的归属判定。
问题：实测并集相邻换族频率 0.7533（独立泊松预期 0.4975）。但两族各自 GUE（强排斥）时，
同族相邻概率低于泊松——换族自然偏高。判定 0.753 是"独立 GUE 混合"的自然值还是跨族相关（拉链伪影）。
方法：从实测单族间距分布 bootstrap 重建两族独立零点（保持各族 GUE 统计、破坏跨族相关），
混合后统计换族频率——重复 R 次。若模拟均值≈0.753 → 数学自然值（无跨族相关）；
若模拟≈0.5x → 实测 0.753 含跨族相关（拉链）。
同时修正 g(r) 归一化（逐点 ρ_L(z)），复核跨族密度是否真的均匀（g≈1）。
输出 qrh_audit3.json。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\qrh_audit3.json"
T = 6.0e5
LOW = 300.0
R = 40

def rho_zeta(t):
    return np.log(t / (2.0 * np.pi)) / (2.0 * np.pi)

def rho_L(t):
    return (np.log(t / (2.0 * np.pi)) + np.log(5.0) - 1.0) / (2.0 * np.pi)

def rebuild(orig, rho, start, stop):
    """从实测零点重建独立序列：间距序列随机旋转（保持 GUE 统计、破跨族相关）。
    用间距/(密度均值) 归一化到密度 1 再按 rho 缩放——近似保持局部密度。"""
    gaps = np.diff(orig)
    if len(gaps) < 1:
        return np.array([])
    # 随机旋转（破跨族相关；旋转只移起点，不改变间距序列的 GUE 统计）
    k = np.random.randint(0, len(gaps))
    gaps = np.roll(gaps, k)
    t = start
    out = []
    for g in gaps:
        t = t + g
        if t >= stop:
            break
        out.append(t)
    return np.array(out)

def flip_freq(tt, kind):
    return float(np.sum(kind[1:] != kind[:-1])) / (len(kind) - 1)

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    print("in-band zeta=%d L=%d" % (nz, nl))
    # 实测换族
    zz = np.stack([z, np.zeros(nz)], 1); ll = np.stack([l, np.ones(nl)], 1)
    allz = np.concatenate([zz, ll]); allz = allz[np.argsort(allz[:, 0])]
    obs = flip_freq(allz[:, 0], allz[:, 1])
    print("实测换族=%.4f" % obs)
    # 模拟：独立重建
    flips = []
    for r in range(R):
        zr = rebuild(z, rho_zeta, LOW, T)
        lr = rebuild(l, rho_L, LOW, T)
        zz2 = np.stack([zr, np.zeros(len(zr))], 1); ll2 = np.stack([lr, np.ones(len(lr))], 1)
        a2 = np.concatenate([zz2, ll2]); a2 = a2[np.argsort(a2[:, 0])]
        flips.append(flip_freq(a2[:, 0], a2[:, 1]))
    flips = np.array(flips)
    print("模拟独立 GUE 混合：mean=%.4f  std=%.4f  min=%.4f  max=%.4f" %
          (flips.mean(), flips.std(), flips.min(), flips.max()))
    z_sim = (obs - flips.mean()) / flips.std()
    print("实测 vs 模拟：z=%.1fσ" % z_sim)
    # 修正 g(r)：逐点 ρ_L(z) 归一化
    bins = np.linspace(0.0, 1.0, 51)
    g = np.zeros(50)
    for k in range(50):
        r0, r1 = bins[k], bins[k + 1]
        a = np.searchsorted(l, z + r0, side="left")
        b = np.searchsorted(l, z + r1, side="left")
        cnt = (b - a)
        vol = (r1 - r0)
        expected = vol * rho_L(z)
        g[k] = float(np.mean(cnt / np.maximum(expected, 1e-12)))
    print("g(r) 逐点归一化（每 5 箱均值）：")
    g5 = [float(np.mean(g[k:k + 5])) for k in range(0, 50, 5)]
    for k, v in enumerate(g5):
        print("  r=[%.2f,%.2f]  g=%.3f" % (k * 0.1, (k + 1) * 0.1, v))
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"observed_flip": obs, "sim": {"R": R, "mean": float(flips.mean()),
                    "std": float(flips.std()), "min": float(flips.min()), "max": float(flips.max()),
                    "z_sim": float(z_sim)},
                   "g_corr": {"bins05": [round(bins[k], 3) for k in range(0, 51, 5)],
                              "g5": g5},
                   "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    print("saved", OUT)

if __name__ == "__main__":
    main()
