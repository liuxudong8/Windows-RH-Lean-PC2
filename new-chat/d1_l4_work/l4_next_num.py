# -*- coding: utf-8 -*-
"""L4 下一篇核心数值：(1) 跨族交叉项涨落 Delta=S_zetaL-E 的全量计算与符号定向 (T=6e5)；
(2) 条件(D) 检验：zeta 零点局部密度 A(t) 的自相关 C_zeta(h) 衰减与可积性。
输出 JSON + 控制台表。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\d1_l4_work\l4_next_num.json"

def wfun(u):
    return 4.0 / (4.0 + u * u)

def window_sum(roots, t, W, ell):
    lo = np.searchsorted(roots, t - W)
    hi = np.searchsorted(roots, t + W)
    if lo >= hi:
        return 0.0
    u = (roots[lo:hi] - t) * ell
    return float(np.sum(wfun(u)))

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    T = 6.0e5
    ELL = np.log(T)
    R = 20.0
    W = R / ELL
    N_z, N_l = len(z), len(l)
    N_K = N_z + N_l
    print("T=%.0f  ell=%.4f  W=%.4f  N_z=%d  N_l=%d  N_K=%d" % (T, ELL, W, N_z, N_l, N_K))

    # ---------------- Part 1: Delta = S_zetaL - E ----------------
    lo_b = 12.0
    hi_b = T - W
    mask = (l >= lo_b) & (l <= hi_b)
    l_use = l[mask]
    n_use = len(l_use)
    # S = sum over L-zeros of A(gamma')
    S = 0.0
    # 向量化：批量 searchsorted 太慢，用 numpy 分块；每块内逐 t 窗口和
    B = 2000
    s_parts = np.zeros(n_use)
    for i in range(0, n_use, B):
        tb = l_use[i:i + B]
        # 对整块：对每个 t 做窗口和
        for j, tt in enumerate(tb):
            s_parts[i + j] = window_sum(z, tt, W, ELL)
    S = float(np.sum(s_parts))
    # 逐点期望 E[A(gamma')] = log(gamma'/2pi)/ell（局部密度归一）
    E = float(np.sum(np.log(l_use / (2.0 * np.pi)) / ELL))
    Delta = S - E
    # 参考涨落：sqrt(N_l * Var(A))，泊松近邻 Var(A)~1
    sig_ref = np.sqrt(N_l)
    res = {
        "T": T, "ell": ELL, "W": W,
        "N_z": int(N_z), "N_l": int(N_l), "N_K": int(N_K),
        "n_use": int(n_use),
        "S_zetaL": S, "E": E, "Delta": Delta,
        "Delta_over_NK": Delta / N_K,
        "Delta_over_sqrtNl": Delta / sig_ref,
        "sigma_ref": float(sig_ref),
        "blocks": []
    }
    print("S_zetaL=%.1f  E=%.1f  Delta=%.1f  Delta/N_K=%.6f  Delta/sqrt(N_l)=%.4f (ref %.1f)"
          % (S, E, Delta, Delta / N_K, Delta / sig_ref, sig_ref))
    # 分块稳定性
    blocks = np.array_split(l_use, 3)
    print("--- 分块 (S-E)/n ---")
    for i, blk in enumerate(blocks):
        Sb = float(np.sum(window_sum(z, tt, W, ELL) for tt in blk))
        Eb = float(np.sum(np.log(blk / (2.0 * np.pi)) / ELL))
        res["blocks"].append({"i": i, "n": int(len(blk)), "S_minus_E": Sb - Eb,
                              "per_n": (Sb - Eb) / len(blk)})
        print("块%d: n=%d  S-E=%.1f  (S-E)/n=%.5f" % (i, len(blk), Sb - Eb, (Sb - Eb) / len(blk)))

    # ---------------- Part 2: C_zeta(h) 自相关（条件 D）----------------
    # t 网格 [T/2, T]，步长 dt=0.25，中段剔除边界各 10
    dt = 0.25
    tgrid = np.arange(T / 2.0 + 10.0, T - 10.0 - dt, dt)
    Nt = len(tgrid)
    A = np.zeros(Nt)
    for i, tt in enumerate(tgrid):
        A[i] = window_sum(z, tt, W, ELL)
    m = float(np.mean(A)); v = float(np.var(A))
    hs = [0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0]
    corr = []
    for h in hs:
        kh = int(round(h / dt))
        if kh == 0:
            c = float(np.mean((A - m) ** 2))
        else:
            c = float(np.mean((A[:Nt - kh] - m) * (A[kh:] - m)))
        corr.append({"h": h, "C": c})
        print("C_zeta(%.2f)=%.5f" % (h, c))
    # 数值积分 |C|：梯形，分段取 |C|
    hh = np.array([x["h"] for x in corr]); cc = np.array([abs(x["C"]) for x in corr])
    # 外推尾部（>4 按指数衰减率估计，用最后两点对数斜率）
    if cc[-2] > 0 and cc[-1] > 0:
        lam = np.log(cc[-2] / cc[-1]) / (hh[-1] - hh[-2])
        tail = cc[-1] * np.exp(-lam * np.inf)  # 0
        intC = float(np.trapezoid(cc, hh)) if hasattr(np, "trapezoid") else float(np.trapz(cc, hh))
        res["C_zeta"] = {"mean_A": m, "var_A": v, "corr": corr,
                         "int_absC_0to4": intC, "decay_lambda": float(lam)}
        print("mean(A)=%.4f  var(A)=%.4f  int|C|(0..4)=%.4f  尾衰减率 lam=%.3f"
              % (m, v, intC, lam))
    else:
        intC = float(np.trapz(cc, hh))
        res["C_zeta"] = {"mean_A": m, "var_A": v, "corr": corr, "int_absC_0to4": intC}
        print("mean(A)=%.4f  var(A)=%.4f  int|C|(0..4)=%.4f (尾部不可估)" % (m, v, intC))
    res["elapsed"] = time.time() - t0
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(res, f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
