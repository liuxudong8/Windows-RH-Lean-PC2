# -*- coding: utf-8 -*-
"""攻防 XLII · S4 数值件 B：窄核专项实测（λ 路径直接验证）。
λ(T)=(logT)^{−15/7} 在 T∈[1e4,8e5] 落入 a∈[0.0037,0.0086]——现有 a≥0.1 网格只能外推。
本脚本用 half=0.5、binw=0.0005 的细直方图直接测 a∈{0.005,0.01,0.02,0.05,0.1,0.2} 的
A(a;T)、GUE2−1、Δ=A−GUE2、A−1，钉死窄核端标度（GUE2−1~a³ 理论）与符号结构。
主档 T=8e5（zeta_T800000/L_D5_T800000），复核 T=6e5（zeros_T6e5）。
"""
import numpy as np, json, os, time

BASE = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(OUTDIR, "xlii_s4b.json")
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

def pair_hist(z, delta, half, binw):
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
    uc = (np.arange(nb) + 0.5) * binw
    return uc, hist

def A_from_hist(hist, uc, n, a):
    return 1.0 + float(np.sum(hist * K_fejer(uc, a) ** 2)) / n

def gue2_a(a, R=60.0):
    N = 1_200_001
    u = np.linspace(0.0, R, N)
    return 1.0 + 2.0 * float(np.trapezoid((1.0 - sinc(np.pi * u) ** 2) * sinc(np.pi * u / a) ** 4, u))

t0 = time.time()
TABS = [(8.0e5, "zeta_T800000.npz", "L_D5_T800000.npz"),
        (6.0e5, "zeros_T6e5.npz", "zeros_T6e5.npz")]
res_rows = []
for (T, zf, lf) in TABS:
    z = np.sort(np.load(os.path.join(BASE, zf))["zeta"])
    l = np.sort(np.load(os.path.join(BASE, lf))["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    nz, nl = len(z), len(l)
    dz = rho_zeta(np.median(z)); dl = rho_L(np.median(l))
    rec = {"T": T, "n_zeta": nz, "n_L": nl,
           "A": {"zeta": {}, "L": {}}, "GUE2": {},
           "Delta": {"zeta": {}, "L": {}}, "A_minus_1": {"zeta": {}, "L": {}}}
    for tag, arr, dlt in (("zeta", z, dz), ("L", l, dl)):
        uc, hist = pair_hist(arr, dlt, HALF, BINW)
        for a in A_GRID:
            A = A_from_hist(hist, uc, len(arr), a)
            G = gue2_a(a)
            rec["A"][tag][str(a)] = round(A, 9)
            rec["GUE2"][str(a)] = round(G, 9)
            rec["Delta"][tag][str(a)] = round(A - G, 9)
            rec["A_minus_1"][tag][str(a)] = round(A - 1.0, 9)
    print("T=%.0e nz=%d nl=%d %.0fs" % (T, nz, nl, time.time() - t0), flush=True)
    res_rows.append(rec)

# λ 路径落点
lmb_pts = []
for Tt in (1e4, 2e4, 4e4, 1e5, 2e5, 4e5, 6e5, 8e5):
    lmb_pts.append({"T": Tt, "lambda_15_7": round(1.0 / (np.log(Tt) ** (15.0 / 7.0)), 10)})

out = {"meta": {"half": HALF, "binw": BINW, "LOW": LOW, "A_grid": A_GRID,
                "note": "GUE2−1 理论小 a 指数=3（换元 u=ax：2a∫(1−sinc²πax)sinc⁴πx dx → (2π²a³/3)∫x²sinc⁴πx dx）"},
       "rows": res_rows, "lambda_path": lmb_pts}
with open(OUT, "w", encoding="utf-8") as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print("saved:", OUT)
for r_ in res_rows:
    print("T=%.0e" % r_["T"])
    for fam in ("zeta", "L"):
        row = "  %s: " % fam
        for a in A_GRID:
            row += "a=%.3g A-1=%+.2e Δ=%+.2e | " % (a, r_["A_minus_1"][fam][str(a)], r_["Delta"][fam][str(a)])
        print(row)
