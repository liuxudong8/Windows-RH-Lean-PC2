# -*- coding: utf-8 -*-
"""2 倍因子定位：最小几何验证。
测试 1：常数强度 Poisson（窄带内 ρ≈常数），u=Δ·ρ(tmid)，hist.sum()/N 应=窗口 40。
测试 2：u=Δ（ρ≡1），均匀点 [0,N]，hist.sum()/N 应=窗口 40（纯几何）。
"""
import numpy as np

def sinc(x):
    with np.errstate(divide="ignore", invalid="ignore"):
        x = np.asarray(x, dtype=float)
        return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def rho_fun(t, is_L):
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    base = np.log(t / (2 * np.pi))
    if is_L:
        base = base + np.log(5.0) - 1.0
    return base / (2 * np.pi)

def pair_hist_debug(z, is_L, half, binw, rho_mode="local"):
    n = len(z)
    nb = int(np.ceil(half / binw)) + 1
    hist = np.zeros(nb, dtype=np.float64)
    win_raw = half / 0.5
    chunk = 300000
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
        if rho_mode == "local":
            u = ds * rho_fun(tm, is_L)
        elif rho_mode == "one":
            u = ds
        else:
            raise ValueError(rho_mode)
        u = u[(u > 1e-12) & (u < half)]
        hist += np.histogram(u, bins=nb, range=(0.0, half))[0]
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist, n

# ---- 测试 1：窄带常数强度 Poisson ----
rng = np.random.default_rng(7)
LOW, T = 5.9e5, 6.0e5
rho_c = rho_fun(np.array([(LOW + T) / 2]), False)[0]
N1 = int((T - LOW) * rho_c)
pts = np.sort(LOW + (T - LOW) * rng.random(N1))
uc, h1, n1 = pair_hist_debug(pts, False, 40.0, 0.02, "local")
print("测试1 常数强度 Poisson: n=%d 期望 hist.sum()/N=40（Poisson ρ₂=1）" % n1)
print("  hist.sum()=%d  hist.sum()/N=%.4f  理论 40" % (h1.sum(), h1.sum() / n1))
print("  u<10 计数/N=%.4f  理论 10" % (h1[:500].sum() / n1))

# ---- 测试 2：ρ≡1，均匀点 [0,N]，u=Δ ----
N2 = 200000
pts2 = np.sort(N2 * rng.random(N2))   # 密度 1，区间长 N2 → ρ=1
# 窗口 u<40（=Δ<40）：需 win_raw≥40，用 half=40, win_raw=40/0.5=80 足够
uc, h2, n2 = pair_hist_debug(pts2, False, 40.0, 0.02, "one")
print("\n测试2 均匀点 ρ=1, u=Δ: n=%d hist.sum()/N=%.4f  理论 40（Poisson ρ₂=1）" % (n2, h2.sum() / n2))
print("  u<10 计数/N=%.4f  理论 10" % (h2[:500].sum() / n2))

# ---- 测试 3：完全解析核对 ∫sinc⁴ ----
a = 1.0
N3 = 2_000_001
u = np.linspace(0, 40, N3)
I = np.trapezoid(sinc(np.pi * u / a) ** 4, u)
print("\n∫₀^40 sinc⁴(πu)du = %.6f  （理论 a/3=%.6f, 2a/3=%.6f）" % (I, a / 3, 2 * a / 3))
