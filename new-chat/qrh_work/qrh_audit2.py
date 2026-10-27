# -*- coding: utf-8 -*-
"""QRH 常数机制攻坚 · 数值定向 #2：并集整体拟随机性与拉链化稳定性审计。
审计 #1 发现：两族族内 GUE 兼容，但跨族序列偏拉链化（换族 0.753 vs 独立 0.498）。
本件判定：
(i)   并集整体最近邻（正确归一化：并集密度 ρ_ζ+ρ_L）vs GUE/泊松——若 GUE（排斥）→ 并集整体拟随机；
      若泊松/亚泊松 → 混合抵消排斥（跨族拉链的产物）；
(ii)  换族频率随 T 分段——恒定（方法层一致：伪影或全局结构）vs 演化（数学结构）；
(iii) 跨族最近邻与并集最近邻随 T 分段——拉链化的短程结构稳定性；
(iv)  并集最近邻 p(0+)、小 s 指数随 T——并集排斥性是否有 T 依赖。
输出 qrh_audit2.json。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\qrh_audit2.json"
T_LIST = [1.0e5, 2.0e5, 3.0e5, 4.0e5, 5.0e5, 6.0e5]

def rho_zeta(t):
    return np.log(t / (2.0 * np.pi)) / (2.0 * np.pi)

def rho_L(t):
    return (np.log(t / (2.0 * np.pi)) + np.log(5.0) - 1.0) / (2.0 * np.pi)

def nn_stats(s, label, n_bin=40, s_max=4.0):
    s = np.asarray(s, dtype=float); s = s[np.isfinite(s)]
    mean = float(s.mean()); var = float(s.var())
    small = s[s < 0.1]
    p0 = float(len(small) / len(s) / 0.1) if len(s) else float("nan")
    ss = s[s < 0.3]
    if len(ss) > 20:
        bc = np.bincount(np.clip((ss / 0.005).astype(int), 0, 59), minlength=60)[0:60]
        xb = (np.arange(60) + 0.5) * 0.005
        m = bc > 0
        a = float(np.polyfit(np.log(xb[m]), np.log(bc[m]), 1)[0])
    else:
        a = float("nan")
    print("  %-16s n=%7d mean=%.4f var=%.4f p(0+)=%.3f s-exp=%.2f"
          % (label, len(s), mean, var, p0, a))
    return {"n": int(len(s)), "mean": mean, "var": var, "p0plus": p0, "small_s_exp": a}

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z_full = np.sort(d["zeta"]); l_full = np.sort(d["L"])
    res = {"by_T": []}
    for T in T_LIST:
        z = z_full[z_full <= T]; l = l_full[l_full <= T]
        nz, nl = len(z), len(l)
        # 并集合并
        zz = np.stack([z, np.zeros(nz)], 1); ll = np.stack([l, np.ones(nl)], 1)
        allz = np.concatenate([zz, ll]); allz = allz[np.argsort(allz[:, 0])]
        tt = allz[:, 0]; kind = allz[:, 1]
        dt = np.diff(tt)
        # 最近邻（两侧最小）
        nn = np.minimum(dt, np.concatenate([[np.inf], dt[:-1]]))
        nn = np.concatenate([nn, [np.inf]])[:-1] if False else nn
        mid = (tt[:-1] + tt[1:]) / 2.0
        rho_u = rho_zeta(mid) + rho_L(mid)
        s_u = nn * rho_u
        # 换族频率
        flips = float(np.sum(kind[1:] != kind[:-1])) / (len(kind) - 1)
        p_ind = 2.0 * (nz / (nz + nl)) * (nl / (nz + nl))
        # 跨族最近邻（ζ→L）
        idx = np.searchsorted(l, z, side="right"); idx = np.clip(idx, 1, len(l) - 1)
        dL = np.minimum(np.abs(l[idx] - z), np.abs(l[idx - 1] - z))
        s_cross = dL * rho_L(z)
        # 并集最近邻对照（归一化到均值 1）
        s_u1 = s_u / s_u.mean()
        rec = {"T": T, "nz": nz, "nl": nl, "N_K": nz + nl,
               "flip_freq": flips, "flip_independent_pred": p_ind,
               "flip_z": (flips - p_ind) / np.sqrt(p_ind * (1.0 - p_ind) / (len(kind) - 1)),
               "union_nn_mean_unit": float(s_u.mean()), "union_nn_var_unit": float(s_u.var()),
               "cross_nn_mean_unit": float(s_cross.mean()), "cross_nn_var_unit": float(s_cross.var())}
        print("T=%.0f 换族=%.4f(独立%.4f,z=%.0fσ) 并集NN mean=%.4f var=%.4f 跨族NN mean=%.4f var=%.4f"
              % (T, flips, p_ind, rec["flip_z"], s_u.mean(), s_u.var(), s_cross.mean(), s_cross.var()))
        rec["union_nn"] = nn_stats(s_u1, "union_nn_norm1", s_max=4.0)
        res["by_T"].append(rec)
    ref = {"GUE": {"var": 0.178, "p0plus": 0.0, "small_s_exp": 2.0},
           "poisson": {"var": 1.0, "p0plus": 1.0, "small_s_exp": 1.0},
           "note": "union_nn_norm1 归一化到均值 1（GUE/泊松的 mean=1 口径）"}
    res["reference"] = ref
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"results": res, "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
