# -*- coding: utf-8 -*-
"""S5 跨族对照：ζ × 独立 Poisson（密度=ρ̄_L）应回到独立预测 0.37a。
若 ζ×L 实测 0.72a ≠ ζ×Poisson 0.37a ⟹ 跨族聚集真实信号（非密度/口径伪影）。"""
import numpy as np, json, os, time

BASE = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
LOW, HIGH = 300.0, 8.0e5
HALF, BINW = 0.5, 0.0005
A_GRID = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2]
RNG = np.random.default_rng(20261025)

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
            if H - L > 0:
                segs.append(np.abs(l[L:H] - za[i]))
        if not segs:
            continue
        ds = np.concatenate(segs)
        ds = ds[ds > 1e-12]
        hist += np.histogram(ds * delta, bins=nb, range=(0.0, half * delta))[0]
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist

def A_cross(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * sinc(np.pi * uc / a) ** 4)) / n

t0 = time.time()
z = np.sort(np.load(os.path.join(BASE, "zeta_T800000.npz"))["zeta"])
l = np.sort(np.load(os.path.join(BASE, "L_D5_T800000.npz"))["L"])
z = z[(z >= LOW) & (z <= HIGH)]; l = l[(l >= LOW) & (l <= HIGH)]
nz, nl = len(z), len(l)
rz = rho_zeta(np.median(z)); rl = rho_L(np.median(z))
delta = rz; umax = HALF * delta

# 独立预测（窗口积分，因子 2：两侧邻居密度 2ρ_L）
def ind_win(a, dens_ratio):
    N = 1_200_001
    u = np.linspace(0.0, umax, N)
    return 1.0 + 2.0 * dens_ratio * float(np.trapezoid(sinc(np.pi * u / a) ** 4, u))

# 对照 1：均匀 Poisson（n=nl 个点，密度 ρ̄=nl/(HIGH-LOW)）
npoi = nl
P = np.sort(RNG.uniform(LOW, HIGH, npoi))
rhoP = npoi / (HIGH - LOW)
ucP, histP = pair_hist_cross(z, P, delta, HALF, BINW)
# 对照 2：L 逐点随机位移 ±0.25（破坏互相关、保持密度），再打乱
Lsh = np.sort(l + RNG.uniform(-0.25, 0.25, nl))
# 边界回夹
Lsh = np.clip(Lsh, LOW, HIGH)
ucS, histS = pair_hist_cross(z, Lsh, delta, HALF, BINW)
ucL, histL = pair_hist_cross(z, l, delta, HALF, BINW)

print("nz=%d nl=%d rz=%.4f rl=%.4f rhoP=%.4f" % (nz, nl, rz, rl, rhoP))
rows = {"T": HIGH, "A_cross_L": {}, "A_cross_Poisson": {}, "A_cross_Lshuf": {},
        "ind_win_Lratio": {}, "ind_win_Pratio": {}}
for a in A_GRID:
    s = str(a)
    AL = A_cross(histL, ucL, nz, a)
    AP = A_cross(histP, ucP, nz, a)
    AS = A_cross(histS, ucS, nz, a)
    IL = ind_win(a, rl / rz)
    IP = ind_win(a, rhoP / rz)
    rows["A_cross_L"][s] = round(AL, 9)
    rows["A_cross_Poisson"][s] = round(AP, 9)
    rows["A_cross_Lshuf"][s] = round(AS, 9)
    rows["ind_win_Lratio"][s] = round(IL, 9)
    rows["ind_win_Pratio"][s] = round(IP, 9)
    print("a=%.3g  ζ×L=%+.3e  ζ×Poisson=%+.3e  ζ×Lshuf=%+.3e  独立L=%+.3e 独立P=%+.3e" %
          (a, AL-1, AP-1, AS-1, IL-1, IP-1), flush=True)
print("elapsed %.0fs" % (time.time()-t0))
with open(os.path.join(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work", "xlii_s5_ctl.json"),
          "w", encoding="utf-8") as f:
    json.dump(rows, f, ensure_ascii=False, indent=1)
