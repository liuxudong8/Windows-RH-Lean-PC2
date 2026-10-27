# -*- coding: utf-8 -*-
"""S0 v2 查错检验：Poisson 模拟对照 + ρ₂(u) 实测曲线。
若 pair_hist_local 代码正确，Poisson 模拟（同密度分布）应给出 A≈1+a/3（理论）。
并输出实测 ρ₂(u)=hist(u)/(N·Δu) vs GUE 1−sinc²(πu) vs Poisson 1 的曲线数据。
"""
import numpy as np, time
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
T = 6.0e5
LOW = 300.0
plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei"]
plt.rcParams["axes.unicode_minus"] = False


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


def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2


def pair_hist_local(z, is_L, half, binw):
    n = len(z)
    nb = int(np.ceil(half / binw)) + 1
    hist = np.zeros(nb, dtype=np.float64)
    win_raw = half / 0.5
    chunk = 200000
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
        u = ds * rho_fun(tm, is_L)
        u = u[(u > 1e-12) & (u < half)]
        hist += np.histogram(u, bins=nb, range=(0.0, half))[0]
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist, n


def A_from_hist(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n


def make_poisson(seed=42):
    """ζ 密度的非齐次 Poisson 点过程：[300,6e5]，强度 ρ(t)=log(t/2π)/(2π)。逆变换采样。"""
    rng = np.random.default_rng(seed)
    Lam = lambda t: (t * np.log(t / (2 * np.pi)) - t) / (2 * np.pi)
    Lam0, Lam1 = Lam(LOW), Lam(T)
    N = rng.poisson(Lam1 - Lam0)
    uu = rng.uniform(0.0, 1.0, N)
    # 数值求逆 Λ(t)=Λ0+u(Λ1−Λ0)：二分/牛顿。用插值：预建网格
    grid = np.linspace(LOW, T, 200001)
    Lg = Lam(grid)
    target = Lam0 + uu * (Lam1 - Lam0)
    idx = np.searchsorted(Lg, target)
    idx = np.clip(idx, 1, len(grid) - 1)
    t1 = grid[idx - 1]; t2 = grid[idx]
    L1 = Lg[idx - 1]; L2 = Lg[idx]
    pts = t1 + (target - L1) / (L2 - L1 + 1e-30) * (t2 - t1)
    return np.sort(pts)


def main():
    t0 = time.time()
    # 1) Poisson 模拟对照
    poi = make_poisson()
    print("Poisson n=%d (预测 Λ1−Λ0=%.0f)" % (len(poi), (lambda t: (t * np.log(t / (2 * np.pi)) - t) / (2 * np.pi))(T) - (lambda t: (t * np.log(t / (2 * np.pi)) - t) / (2 * np.pi))(LOW)))
    uc, hp, np_ = pair_hist_local(poi, False, 40.0, 0.02)
    print("--- Poisson 模拟 A(a) vs 理论 1+a/3 ---")
    for a in [0.5, 1.0, 2.0, 4.0, 8.0]:
        A_sim = A_from_hist(hp, uc, np_, a)
        print("a=%.1f  A_sim=%.4f  1+a/3=%.4f  diff=%.4f" % (a, A_sim, 1 + a / 3, A_sim - (1 + a / 3)))

    # 2) 实测 ρ₂(u) 曲线（ζ）
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); z = z[(z >= LOW) & (z <= T)]
    uc2, hz2, nz = pair_hist_local(z, False, 40.0, 0.02)
    rho2_obs = hz2 / (nz * 0.02)          # 有序对密度 / N → ρ₂(u)
    gue = 1.0 - sinc(np.pi * uc2) ** 2
    print("\n--- ρ₂(u) 实测 vs GUE/Poisson（抽样点）---")
    for uu in [0.2, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 39.0]:
        k = int(uu / 0.02)
        print("u=%.1f  ρ2_obs=%.3f  GUE=%.3f  Poisson=1.000" % (uu, rho2_obs[k], gue[k]))
    print("ρ2_obs 均值(u<10)=%.4f  总计数=%d  N·∫ρ2(0,40)=%.0f" % (
        np.mean(rho2_obs[:500]), int(np.sum(hz2)), nz * 40))

    # 图
    fig, ax = plt.subplots(1, 2, figsize=(13, 5))
    ax[0].plot(uc2, rho2_obs, lw=0.8, color="k", label="实测 ρ₂(u)（ζ, T=6e5）")
    ax[0].plot(uc2, gue, lw=1.2, color="b", label="GUE: 1−sinc²(πu)")
    ax[0].axhline(1.0, color="r", ls="--", lw=1.0, label="Poisson: 1")
    ax[0].set_xlim(0, 40); ax[0].set_ylim(-0.2, 3.5)
    ax[0].set_xlabel("u（局部归一化间距）"); ax[0].set_ylabel("ρ₂(u)")
    ax[0].set_title("实测配对密度 vs GUE / Poisson"); ax[0].legend(fontsize=9)
    ax[1].plot(uc2[:1000], rho2_obs[:1000], lw=0.8, color="k", label="实测")
    ax[1].plot(uc2[:1000], gue[:1000], lw=1.2, color="b", label="GUE")
    ax[1].axhline(1.0, color="r", ls="--", lw=1.0, label="Poisson")
    ax[1].set_xlim(0, 20); ax[1].set_ylim(-0.2, 3.5)
    ax[1].set_xlabel("u"); ax[1].set_ylabel("ρ₂(u)")
    ax[1].set_title("u∈[0,20] 放大"); ax[1].legend(fontsize=9)
    fig.suptitle("S0 查错：ρ₂ 实测 vs GUE / Poisson（ζ）", fontsize=13)
    fig.tight_layout()
    fig.savefig(OUTDIR + r"\xlii_s0_check_rho2.png", dpi=150)
    print("\n图已存 xlii_s0_check_rho2.png  elapsed %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
