# -*- coding: utf-8 -*-
"""S5 跨族数值件 C 调试：验证独立预测积分与双方向对称性。"""
import numpy as np, os

BASE = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
LOW = 300.0
HALF, BINW = 0.5, 0.0005

def sinc(x):
    x = np.asarray(x, dtype=float)
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def rho_zeta(t):
    return np.log(np.maximum(np.asarray(t, dtype=float), 10.0) / (2 * np.pi)) / (2 * np.pi)

def rho_L(t):
    return (np.log(np.maximum(np.asarray(t, dtype=float), 10.0) / (2 * np.pi)) + np.log(5.0)) / (2 * np.pi)

def pair_hist_cross(z, l, delta, half, binw):
    n = len(z)
    nb = int(np.ceil(half * delta / binw)) + 1
    hist = np.zeros(nb, dtype=np.float64)
    chunk = 300000
    for a0 in range(0, n, chunk):
        a1 = min(a0 + chunk, n)
        za = z[a0:a1]
        lo = np.searchsorted(l, za - half, side="left")
        hi = np.searchsorted(l, za + half, side="right")
        segs = []
        for i in range(a1 - a0):
            L, H = lo[i], hi[i]
            if H - L > 1:
                segs.append(np.abs(l[L:H] - za[i]))
        if not segs:
            continue
        ds = np.concatenate(segs)
        ds = ds[ds > 1e-12]
        hist += np.histogram(ds * delta, bins=nb, range=(0.0, half * delta))[0]
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist

# 手动独立预测积分（高精度）
def manual_int(a, umax, N=4_000_001):
    u = np.linspace(0.0, umax, N)
    return float(np.trapezoid(sinc(np.pi * u / a) ** 4, u))

z = np.sort(np.load(os.path.join(BASE, "zeta_T800000.npz"))["zeta"])
l = np.sort(np.load(os.path.join(BASE, "L_D5_T800000.npz"))["L"])
z = z[(z >= LOW) & (z <= 8.0e5)]; l = l[(l >= LOW) & (l <= 8.0e5)]
nz, nl = len(z), len(l)
rz = rho_zeta(np.median(z)); rl = rho_L(np.median(l))
delta = rz
umax = HALF * delta
print("nz=%d nl=%d rz=%.6f rl=%.6f umax=%.6f" % (nz, nl, rz, rl, umax))

for a in (0.005, 0.01, 0.02, 0.05, 0.1, 0.2):
    m = manual_int(a, umax)
    print("a=%.3g manual_int(0..umax)=%.6e  全积分 (2/3)a=%.6e  ratio=%.4f" % (a, m, (2.0/3.0)*a, m/((2.0/3.0)*a)))

uc, h1 = pair_hist_cross(z, l, delta, HALF, BINW)
uc2, h2 = pair_hist_cross(l, z, delta, HALF, BINW)
print("S_zeta_center = %.0f   S_L_center = %.0f   ratio=%.4f" % (h1.sum(), h2.sum(), h1.sum()/h2.sum()))
print("nb1=%d nb2=%d" % (len(h1), len(h2)))
# 期望对数（窗口内，全对）
expected_pairs = nz * (2 * HALF * rl)  # 每 ζ 中心邻域期望 L 邻居数（物理窗口 2*half，密度 rl）
print("期望跨族对数 (全窗口) ≈ %.0f；实测 hist 总对数=%.0f；滤除比例=%.3f" %
      (expected_pairs, h1.sum(), h1.sum()/expected_pairs))
