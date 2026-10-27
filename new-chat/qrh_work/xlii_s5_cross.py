# -*- coding: utf-8 -*-
"""攻防 XLII · S5 数值件 C：跨族交叉配对常数直接实测（ζ×L(χ₅)）。
检验「跨族 f(0) 专用界」的核心预测：跨族配对无 |α| 排斥项——
独立交叉（Poisson 型）预测 A_cross(a)−1 ≈ (ρ_L/ρ_ζ)·∫sinc⁴(πu/a)du（线性于 a，无排斥修正）；
若实测系统性低于独立预测 ⟹ 跨族互斥直接信号（并集配对负偏的交叉来源）。
口径与 S4 相同：核平方权重 sinc⁴(πu/a)，u=|Δ|·δ，half=0.5（物理窗口）、binw=0.0005，
a∈{0.005,0.01,0.02,0.05,0.1,0.2}；主档 T=8e5（zeta_T800000/L_D5_T800000），复核 T=6e5。
"""
import numpy as np, json, os, time

BASE = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(OUTDIR, "xlii_s5_cross.json")
LOW = 300.0
HALF, BINW = 0.5, 0.0005
A_GRID = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2]

def sinc(x):
    x = np.asarray(x, dtype=float)
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def rho_zeta(t):
    return np.log(np.maximum(np.asarray(t, dtype=float), 10.0) / (2 * np.pi)) / (2 * np.pi)

def rho_L(t):
    return (np.log(np.maximum(np.asarray(t, dtype=float), 10.0) / (2 * np.pi)) + np.log(5.0)) / (2 * np.pi)

def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2

def pair_hist_cross(z, l, delta, half, binw):
    """对每个 ζ 零点，收集邻域内 L 零点的 |Δ|·δ 距离直方图（计数）。
    全对口径：收集 ≥1 个邻居的中心（不滤除单邻居，保证 S 对称）。"""
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

def A_cross_from_hist(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n

def ind_pred(a, rl, rz, umax, R=60.0):
    """独立交叉预测（窗口 [0,umax]，Poisson 型，无排斥修正）：
    A−1=2·(ρ_L/ρ_ζ)·∫₀^{umax}sinc⁴(πu/a)du——因子 2 来自窗口两侧邻居（|Δ| 密度=2ρ_L）。
    注：∫₀^∞sinc⁴(πu/a)du=a/3（标准值）。"""
    N = 1_200_001
    u = np.linspace(0.0, umax, N)
    integ = sinc(np.pi * u / a) ** 4
    return 1.0 + 2.0 * (rl / rz) * float(np.trapezoid(integ, u))

def ind_pred_full(a, rl, rz):
    """全积分独立预测：A−1=2(ρ_L/ρ_ζ)·a/3（∫₀^∞sinc⁴(πu/a)du=a/3）。"""
    return 1.0 + 2.0 * (rl / rz) * a / 3.0

t0 = time.time()
TABS = [(8.0e5, "zeta_T800000.npz", "L_D5_T800000.npz"),
        (6.0e5, "zeros_T6e5.npz", "zeros_T6e5.npz")]
res_rows = []
for (T, zf, lf) in TABS:
    z = np.sort(np.load(os.path.join(BASE, zf))["zeta"])
    l = np.sort(np.load(os.path.join(BASE, lf))["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    rz = rho_zeta(np.median(z)); rl = rho_L(np.median(l))
    delta = rz  # 与 S4 同口径：u 用 ζ 密度归一化
    umax = HALF * delta
    uc, hist = pair_hist_cross(z, l, delta, HALF, BINW)
    # 对称方向（L 为中心找 ζ），合并验证对称性
    uc2, hist2 = pair_hist_cross(l, z, delta, HALF, BINW)
    rec = {"T": T, "n_zeta": nz, "n_L": nl, "rho_zeta": rz, "rho_L": rl,
           "umax": umax, "A_cross": {}, "A_cross_sym": {}, "ind_pred_win": {},
           "ind_pred_full": {}, "Delta_cross": {}, "Delta_cross_sym": {}}
    for a in A_GRID:
        A = A_cross_from_hist(hist, uc, nz, a)
        As = A_cross_from_hist(hist2, uc2, nl, a)
        Ip = ind_pred(a, rl, rz, umax)
        Ipf = ind_pred_full(a, rl, rz)
        rec["A_cross"][str(a)] = round(A, 9)
        rec["A_cross_sym"][str(a)] = round(As, 9)
        rec["ind_pred_win"][str(a)] = round(Ip, 9)
        rec["ind_pred_full"][str(a)] = round(Ipf, 9)
        rec["Delta_cross"][str(a)] = round(A - Ip, 9)      # 实测 vs 窗口独立预测
        rec["Delta_cross_sym"][str(a)] = round(As - Ip, 9)
    print("T=%.0e nz=%d nl=%d %.0fs" % (T, nz, nl, time.time() - t0), flush=True)
    res_rows.append(rec)

out = {"meta": {"half": HALF, "binw": BINW, "LOW": LOW, "A_grid": A_GRID,
                "note": "跨族交叉配对 A_cross=1+Σ_{ζ×L}sinc⁴(πu/a)/n，u=|Δ|·ρ_ζ；独立预测=Poisson 型（无排斥修正）"},
       "rows": res_rows}
with open(OUT, "w", encoding="utf-8") as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print("saved:", OUT)
for r_ in res_rows:
    print("T=%.0e" % r_["T"])
    for a in A_GRID:
        s = str(a)
        print("  a=%.3g A_cross-1=%+.2e 对称=%+.2e 独立窗口=%+.2e 独立全积分=%+.2e Δ_cross=%+.2e" %
              (a, r_["A_cross"][s] - 1.0, r_["A_cross_sym"][s] - 1.0,
               r_["ind_pred_win"][s] - 1.0, r_["ind_pred_full"][s] - 1.0,
               r_["Delta_cross"][s]))
