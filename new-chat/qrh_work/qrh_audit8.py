# -*- coding: utf-8 -*-
"""QRH 攻坚 · 数值定向 #8：拟随机前提的可靠性审计（子区间收敛 + 反驳扫描）。
(a) 子区间收敛：T=6e5 内 5 段（300-1.2e5/1.2-2.4e5/2.4-3.6e5/3.6-4.8e5/4.8-6e5），每段重算
    GUE 统计量（归一化最近邻 mean/var、s-exp 指数、p(0+)、配对常数 A(fejer_a1.0/a0.5)），
    检验随高度收敛（有限 T 效应标定）；
(b) 反驳扫描：归一化间距带 [0.1,0.3]/[0.3,0.7]/[0.7,1.2]/[1.2,2]/[2,3]/[3,5] 的对计数
    vs GUE 预测 ∫(1−sinc²(πs))·(区间长度·密度)——chi² 型偏差；
(c) 最长间距 vs GUE 预期尺度。
输出 qrh_audit8.json。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\qrh_audit8.json"
T = 6.0e5
LOW = 300.0
SEGS = [(300, 1.2e5), (1.2e5, 2.4e5), (2.4e5, 3.6e5), (3.6e5, 4.8e5), (4.8e5, 6.0e5)]

def sinc(x):
    x = np.asarray(x, dtype=float)
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / x)

def rho_fun(t, is_L):
    """零点密度：ζ 与 L(χ₅)（χ mod 5）。L 含模因子：ρ=(1/2π)[log(t/2π)+log q −1]（audit1 口径）。"""
    t = np.maximum(np.asarray(t, dtype=float), 10.0)
    base = np.log(t / (2 * np.pi))
    if is_L:
        base = base + np.log(5.0) - 1.0
    return base / (2 * np.pi)

def K_fejer(u, a):
    return sinc(np.pi * u / a) ** 2

def stats_block(z, label, is_L):
    """归一化最近邻统计 + 小 s 指数 + p(0+) + 长尾 + 配对常数 A。"""
    n = len(z)
    if n < 100:
        return None
    dnn = np.diff(z)
    dnn = dnn[dnn > 0]
    tmid = 0.5 * (z[:-1] + z[1:])
    rho = rho_fun(tmid, is_L)
    s = dnn * rho
    # 小 s 指数：p(s<ε) ~ C ε^{ν}？——用 log-log 斜率
    eps = 0.05
    frac = np.mean(s < eps)
    frac2 = np.mean(s < 2 * eps)
    s_exp = np.log(frac2 / frac) / np.log(2.0) if frac > 0 else np.nan
    # GUE 对照：mean=1, var≈0.165（Wigner 最近邻近似 var~0.165）
    # p(0+)：GUE 最近邻密度在 0 处 ∝ s^{β}，β≈2（对数气体 β=2）
    # 配对常数 A（fejer 核，δ=logT/(2π)）
    delta = np.log(T) / (2 * np.pi)
    out = {"label": label, "n": n, "nn_mean": float(np.mean(s)), "nn_var": float(np.var(s)),
           "p_below_0.05": float(frac), "s_exp": float(s_exp),
           "max_s": float(np.max(s))}
    for a in [0.5, 1.0]:
        half = 40.0
        binw = 0.02
        nb = int(np.ceil(half * delta / binw)) + 1
        hist = np.zeros(nb)
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
            if segs:
                ds = np.concatenate(segs)
                ds = ds[ds > 1e-12]
                hist += np.histogram(ds * delta, bins=nb, range=(0.0, half * delta))[0]
        uc = (np.arange(nb) + 0.5) * binw
        val = K_fejer(uc, a)
        out["A_fejer_a%.1f" % a] = 1.0 + float(np.sum(hist * val ** 2)) / n
    return out

def wigner_b2(s):
    """GUE 最近邻分布（Wigner surmise, β=2）：p(s)=(32/π²)s²exp(−(4/π)s²)。"""
    s = np.asarray(s, dtype=float)
    return (32.0 / np.pi ** 2) * s * s * np.exp(-4.0 * s * s / np.pi)

def band_check(z, label, is_L):
    """归一化最近邻间距带计数 vs GUE Wigner 预测。"""
    n = len(z)
    dnn = np.diff(z)
    dnn = dnn[dnn > 0]
    tmid = 0.5 * (z[:-1] + z[1:])
    s = dnn * rho_fun(tmid, is_L)
    bands = [(0.1, 0.3), (0.3, 0.7), (0.7, 1.2), (1.2, 2.0), (2.0, 3.0), (3.0, 5.0)]
    rows = []
    for (a, b) in bands:
        obs = np.sum((s >= a) & (s < b))
        grid = np.linspace(a, b, 2001)
        p_integ = np.trapezoid(wigner_b2(grid), grid)
        pred = p_integ * n
        rows.append({"band": [a, b], "obs": int(obs), "pred_gue_wigner": float(pred),
                     "z": float((obs - pred) / np.sqrt(np.maximum(pred, 1.0)))})
    return rows

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    seg_res = {}
    for (lo_, hi_) in SEGS:
        key = "%d-%d" % (lo_, hi_)
        seg_res[key] = {
            "zeta": stats_block(z[(z >= lo_) & (z < hi_)], "zeta_" + key, False),
            "L": stats_block(l[(l >= lo_) & (l < hi_)], "L_" + key, True)}
    full = {"zeta": stats_block(z, "zeta_full", False), "L": stats_block(l, "L_full", True)}
    bands = {"zeta": band_check(z, "zeta", False), "L": band_check(l, "L", True)}
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"segs": seg_res, "full": full, "bands": bands,
                   "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    # 打印
    for key, v in seg_res.items():
        for fam in ("zeta", "L"):
            b = v[fam]
            if b:
                print("%s %s: n=%d nn_mean=%.3f nn_var=%.3f p005=%.4f s_exp=%.2f A0.5=%.3f A1.0=%.3f max_s=%.2f"
                      % (key, fam, b["n"], b["nn_mean"], b["nn_var"], b["p_below_0.05"],
                         b["s_exp"], b["A_fejer_a0.5"], b["A_fejer_a1.0"], b["max_s"]))
    print("--- full ---")
    for fam in ("zeta", "L"):
        b = full[fam]
        print("%s: nn_mean=%.3f nn_var=%.3f p005=%.4f s_exp=%.2f A0.5=%.3f A1.0=%.3f max_s=%.2f"
              % (fam, b["nn_mean"], b["nn_var"], b["p_below_0.05"], b["s_exp"],
                 b["A_fejer_a0.5"], b["A_fejer_a1.0"], b["max_s"]))
    print("--- bands (obs vs GUE pred, z) ---")
    for fam in ("zeta", "L"):
        for r in bands[fam]:
            print("%s band%s obs=%d pred=%.0f z=%.2f" % (fam, r["band"], r["obs"], r["pred_gue_wigner"], r["z"]))
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
