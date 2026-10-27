# -*- coding: utf-8 -*-
"""QRH 常数机制攻坚 · 数值定向 #6：Montgomery–Taylor 变分问题的拟随机版（最优核扫描）。
框架：Proposition 2.1（实轴口径确认：Z_T 元素 z=−γL/2π 实值，配对和 ΣK((γ−γ')δ)²）。
- 无条件族（λ≤1/2，BGS 覆盖）：C_MT=1.3275（最优核 f₀(x)=cos(√2x)/(√2 sin(1/√2))，支撑 [−1/2,1/2]）
- 拟随机版：放宽谱支撑 λ 扫描，实测配对常数 A(K)=ΣK(δΔ)²/N——GUE 排斥压低配对和
- 目标：求 A_min（ζ、L、并集），对照 C_MT=1.3275 与 7/8 门槛 A≤1.125，量化余量
- 方法：配对间距数组一次算（分块），核族×尺度加权复用；MT 核数值积分校准
输出 qrh_audit6.json。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\qrh_audit6.json"
T = 6.0e5
LOW = 300.0

def sinc(x):
    x = np.asarray(x, dtype=float)
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2

def K_sinc(u, a):
    return sinc(np.pi * u / a)

def K_gauss(u, a):
    return np.exp(-(u / a) ** 2 / 2.0)

def make_K_mt(N=4000, Rmax=60.0):
    """MT 最优核 K_MT(u)=∫_{-1/2}^{1/2} f0(x) cos(2πux) dx，f0(x)=cos(√2x)/(√2 sin(1/√2))。
    返回 (u_grid, K_values)，u_grid 细网格。"""
    s2 = np.sqrt(2.0)
    x = np.linspace(-0.5, 0.5, 40001)
    f0 = np.cos(s2 * x) / (s2 * np.sin(1.0 / s2))
    u = np.linspace(0.0, Rmax, N + 1)
    # 数值积分：对每个 u，∫ f0(x) cos(2π u x) dx（偶函数积分）
    K = np.array([np.trapezoid(f0 * np.cos(2 * np.pi * uu * x), x) for uu in u])
    return u, K

def pair_hist(zeros, delta, half, binw=0.02):
    """配对间距直方图：分块收集 |Δ|∈(0, half]，返回 (bin_edges_u, counts)。
    counts[b] 对应 u 中心 = delta*(bin 中心)。"""
    z = np.asarray(zeros, dtype=float)
    n = len(z)
    nb = int(np.ceil(half * delta / binw)) + 1
    hist = np.zeros(nb, dtype=np.float64)
    chunk = 300000
    for a0 in range(0, n, chunk):
        a1 = min(a0 + chunk, n)
        za = z[a0:a1]
        lo = np.searchsorted(z, za - half, side="left")
        hi = np.searchsorted(z, za + half, side="right")
        segs = []
        for i in range(a1 - a0):
            L, H = lo[i], hi[i]
            if H - L > 1:
                segs.append(np.abs(z[L:H] - za[i]))
        if not segs:
            continue
        ds = np.concatenate(segs)
        ds = ds[ds > 1e-12]
        hist += np.histogram(ds * delta, bins=nb, range=(0.0, half * delta))[0]
    u_centers = (np.arange(nb) + 0.5) * binw
    return u_centers, hist

def pair_A_hist(z, delta, kernels, half, binw=0.02):
    """A(K)=1 + Σ_{Δ>0} K(δΔ)²/N。基于一次直方图，所有核复用。"""
    n = len(z)
    u_centers, hist = pair_hist(z, delta, half, binw)
    out = {}
    for name, kk in kernels:
        if name == "mt":
            ug, kv = kk
            val = np.interp(u_centers, ug, kv)
        else:
            val = kk(u_centers)
        out[name] = 1.0 + float(np.sum(hist * val ** 2)) / n
    return out

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    tt = np.sort(np.concatenate([z, l]))
    delta = np.log(T) / (2.0 * np.pi)
    print("T=%.0f nz=%d nl=%d N_K=%d δ=%.4f" % (T, nz, nl, nz + nl, delta))

    # 核族 × 尺度
    kernels = []
    for a in [0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]:
        kernels.append(("fejer_a%.1f" % a, lambda u, a=a: K_fejer(u, a)))
    for a in [0.5, 1.0, 1.5, 2.0, 3.0]:
        kernels.append(("sinc_a%.1f" % a, lambda u, a=a: K_sinc(u, a)))
    for a in [0.5, 1.0, 1.5, 2.0, 3.0, 4.0]:
        kernels.append(("gauss_a%.1f" % a, lambda u, a=a: K_gauss(u, a)))
    ug, kv = make_K_mt()
    kernels.append(("mt", (ug, kv)))
    half = 40.0   # 核尺度最大 8（u=4a+8=40 截断）+ MT 核

    res = {}
    for label, arr in [("zeta", z), ("L", l), ("union", tt)]:
        A = pair_A_hist(arr, delta, kernels, half)
        res[label] = A
        best = min(A, key=A.get)
        print("\n[%s]  A_min=%.4f  (核 %s)" % (label, A[best], best))
        for name in sorted(A, key=A.get)[:6]:
            print("   %-12s %.4f" % (name, A[name]))

    # 对照
    ref = {"C_MT": 0.5 + np.sqrt(0.5) * (1.0 / np.tan(1.0 / np.sqrt(2.0))),
           "threshold_7over8_A": 1.125, "threshold_7over8_ratio": 0.875,
           "note": "C_MT=1/2+(1/√2)cot(1/√2)=1.3274993…；N₀ˢ/N ≥ 2−A（Prop 2.1，实轴口径）"}
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"delta": delta, "nz": nz, "nl": nl, "N_K": nz + nl,
                   "A": res, "reference": ref, "elapsed": time.time() - t0},
                  f, ensure_ascii=False, indent=1)
    print("\nsaved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
