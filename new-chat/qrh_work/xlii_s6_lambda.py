# -*- coding: utf-8 -*-
"""攻防 XLII · 数值件 D（S6 前置）：λ_eff≤1（谱支撑 λ≤1/2）域最优核配对常数系统实测。
解决「λ_eff≤1 唯一硬卡点」的数值判定：
  - 复验：λ≤1/2 核族内配对常数 A 的实测极小 vs 理论 C_MT=1/2+(1/√2)cot(1/√2)=1.3274992963
  - ε 逼近族：f₀ 尺度 λ=0.5−ε → C_MT 逼近误差 |A−C_MT| 的 10⁻² 级判定
  - 并集分解口径：在线比例 ≥ (N_ζ(2−A_ζ)+N_L(2−A_L))/N_K vs 0.6725−O(10⁻²) 达成判定
口径：audit6 同款（δ=logT/2π、A=1+Σ_{Δ>0}K(δΔ)²/N、half=40）；零点数据双 T（6e5/8e5）。
输出 xlii_s6_lambda.json。
"""
import numpy as np, json, time, os

SCATTER = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(QRH, "xlii_s6_lambda.json")

C_MT = 0.5 + np.sqrt(0.5) * (1.0 / np.tan(1.0 / np.sqrt(2.0)))

def sinc(x):
    x = np.asarray(x, dtype=float)
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def make_K_mt(N=4000, Rmax=60.0):
    """Lamzouri 最优核（λ=1/2）：K_MT(u)=∫_{-1/2}^{1/2} f0(x) cos(2πux) dx，f0=cos(√2x)/(√2 sin(1/√2))。"""
    s2 = np.sqrt(2.0)
    x = np.linspace(-0.5, 0.5, 40001)
    f0 = np.cos(s2 * x) / (s2 * np.sin(1.0 / s2))
    u = np.linspace(0.0, Rmax, N + 1)
    K = np.array([np.trapezoid(f0 * np.cos(2 * np.pi * uu * x), x) for uu in u])
    return u, K

def make_K_scale(lam, N=4000, Rmax=60.0):
    """f₀ 尺度族：f_lam(x)=f0(x/lam)/lam，谱支撑 lam（λ∈{0.3..1.0}），K_lam(0)=1。"""
    s2 = np.sqrt(2.0)
    x = np.linspace(-0.5 * lam, 0.5 * lam, 40001)
    f = np.cos(s2 * x / lam) / (s2 * np.sin(1.0 / s2))
    u = np.linspace(0.0, Rmax, N + 1)
    K = np.array([np.trapezoid(f * np.cos(2 * np.pi * uu * x), x) for uu in u])
    # 归一化 K(0)=1
    return u, K / K[0]

def make_K_mt_eps(eps, N=4000, Rmax=60.0):
    """ε 光滑族：f₀ 端点 eps 过渡窗 w_eps(x)=min(1,(0.5−|x|)/eps)（Lamzouri η_ε 正则化数值模拟），
    f_eps=f₀·w_eps（支撑仍 [−1/2,1/2]），K_eps(0) 归一化。ε→0 逼近最优极限 f₀。"""
    s2 = np.sqrt(2.0)
    x = np.linspace(-0.5, 0.5, 40001)
    f0 = np.cos(s2 * x) / (s2 * np.sin(1.0 / s2))
    w = np.minimum(1.0, (0.5 - np.abs(x)) / eps)
    w = np.clip(w, 0.0, 1.0)
    fe = f0 * w
    u = np.linspace(0.0, Rmax, N + 1)
    K = np.array([np.trapezoid(fe * np.cos(2 * np.pi * uu * x), x) for uu in u])
    return u, K / K[0]

def pair_hist(zeros, delta, half, binw=0.02):
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
            if H - L > 0:
                segs.append(np.abs(z[L:H] - za[i]))
        if not segs:
            continue
        ds = np.concatenate(segs)
        ds = ds[ds > 1e-12]
        hist += np.histogram(ds * delta, bins=nb, range=(0.0, half * delta))[0]
    u_centers = (np.arange(nb) + 0.5) * binw
    return u_centers, hist

def pair_A_hist(z, delta, kernels, half, binw=0.02):
    n = len(z)
    u_centers, hist = pair_hist(z, delta, half, binw)
    out = {}
    for name, kk in kernels:
        ug, kv = kk
        val = np.interp(u_centers, ug, kv)
        out[name] = 1.0 + float(np.sum(hist * val ** 2)) / n
    return out

def main():
    t0 = time.time()
    res = {}
    for T, fz, fl in [
        (6.0e5, os.path.join(SCATTER, "zeros_T6e5.npz"), None),
        (8.0e5, os.path.join(SCATTER, "zeta_T800000.npz"), os.path.join(SCATTER, "L_D5_T800000.npz")),
    ]:
        d = np.load(fz)
        z = np.sort(d["zeta"] if "zeta" in d else d["z"])
        if fl is not None:
            dl = np.load(fl)
            l = np.sort(dl["L"] if "L" in dl else dl["z"])
        else:
            l = np.sort(d["L"])
        z = z[(z >= 300.0) & (z <= T)]; l = l[(l >= 300.0) & (l <= T)]
        nz, nl = len(z), len(l)
        tt = np.sort(np.concatenate([z, l]))
        delta = np.log(T) / (2.0 * np.pi)

        kernels = []
        ug, kv = make_K_mt()
        kernels.append(("mt_lam0.50", (ug, kv)))
        for lam in [0.30, 0.35, 0.40, 0.45, 0.48]:
            ug, kv = make_K_scale(lam)
            kernels.append(("mt_lam%.2f" % lam, (ug, kv)))
        for eps in [0.05, 0.10, 0.20]:
            ug, kv = make_K_mt_eps(eps)
            kernels.append(("mt_eps%.2f" % eps, (ug, kv)))
        half = 40.0

        rT = {"T": T, "delta": delta, "nz": nz, "nl": nl, "N_K": nz + nl, "C_MT": C_MT}
        for label, arr in [("zeta", z), ("L", l), ("union", tt)]:
            A = pair_A_hist(arr, delta, kernels, half)
            rT[label + "_A"] = A
            best = min(A, key=A.get)
            rT[label + "_best"] = (best, A[best])
        # 分解口径在线比例（mt_lam0.50 核，单族各用 C_MT 理论值 + 实测 A）
        Az = rT["zeta_A"]["mt_lam0.50"]; Al = rT["L_A"]["mt_lam0.50"]
        rT["ratio_dec_mt"] = (nz * (2 - Az) + nl * (2 - Al)) / (nz + nl)
        rT["ratio_dec_C_MT"] = 2.0 - C_MT
        rT["dev_mt_zeta"] = abs(Az - C_MT)
        rT["dev_mt_L"] = abs(Al - C_MT)
        res[str(int(T))] = rT
        print("[T=%.0f] nz=%d nl=%d N_K=%d δ=%.4f" % (T, nz, nl, nz + nl, delta))
        for label in ("zeta", "L", "union"):
            A = rT[label + "_A"]
            best, bv = rT[label + "_best"]
            print("  %-5s best=%s A=%.4f   mt_lam0.50=%.4f" % (label, best, bv, A["mt_lam0.50"]))
        print("  C_MT=%.10f  ratio_dec_mt=%.4f  ratio_dec_C_MT=%.4f  dev_ζ=%.2e dev_L=%.2e"
              % (C_MT, rT["ratio_dec_mt"], rT["ratio_dec_C_MT"], rT["dev_mt_zeta"], rT["dev_mt_L"]))

    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"C_MT": C_MT, "note": "λ≤1/2 域最优核实测；A=1+ΣK(δΔ)²/N；δ=logT/2π；half=40",
                   "res": res, "elapsed": time.time() - t0},
                  f, ensure_ascii=False, indent=1)
    print("\nsaved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
