# -*- coding: utf-8 -*-
"""S4 余项精细形态数值定向（第一部分）：在线比例桥余项的 T 依赖标定。
靶心（XIX §6.4/综述 §7(4)）：理论余项界 O(1/√logT)≈0.27 vs 数值余项 10⁻⁵~10⁻³——差距 270 倍未判定。
本件：多 T（1e5→6e5）输出——(i) 密度侧 sup|S_K(t)|（并集计数 vs 主项，XIX 口径）及其 /主项 比值；
(ii) 配对侧 ∫C_ζ(h)dh（A(t) 网格配对负偏积分，l4_multit 口径）——判定余项各项的 T 衰减速率。
主项口径（XIX 修正）：N_K(t)=(t/2π)[log(t/2π)+log 5−1]+7/8 + (t/2π)[log(t/2π)−1] 的并集……——注意：
S_K=S_ζ+S_L 定义：N_ζ=(t/2π)(log(t/2π)−1)+7/8+S_ζ；N_L=(t/2π)(log(t/2π)+log5−1)+S_L。
故主项_K=(t/2π)[2log(t/2π)+log5−2]+7/8。L 数据含 0.27% R-S 趋势伪影（已披露，差分口径免疫）。
输出 detG_rem.json：每 T 的 supS、supS/主项、∫C(h)dh、varA、meanA、W/λ。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entG_work\detG_rem.json"
R = 20.0
T_LIST = [1.0e5, 2.0e5, 3.0e5, 4.0e5, 5.0e5, 6.0e5]

def wfun(u):
    return 4.0 / (4.0 + u * u)

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z_full = np.sort(d["zeta"]); l_full = np.sort(d["L"])
    results = []
    for T in T_LIST:
        ell = np.log(T); W = R / ell
        z = z_full[z_full <= T]; l = l_full[l_full <= T]
        N_z, N_l = len(z), len(l); N_K = N_z + N_l
        # ---- 密度侧：并集计数 vs 主项，t 采样网格 ----
        dt = 1.0
        tgrid = np.arange(50.0, T - 2.0, dt)
        nz = np.searchsorted(z, tgrid, side="right")
        nl = np.searchsorted(l, tgrid, side="right")
        NK = nz + nl
        mainK = (tgrid / (2.0 * np.pi)) * (2.0 * np.log(tgrid / (2.0 * np.pi)) + np.log(5.0) - 2.0) + 7.0 / 8.0
        SK = NK - mainK
        supSK = float(np.max(np.abs(SK)))
        meanN = mainK[-1]
        # ---- 配对侧：A(t) 网格 + C(h) 积分（l4_multit 口径，ζ 谱） ----
        lo_b, hi_b = 12.0, T - W
        l_use = l[(l >= lo_b) & (l <= hi_b)]
        dt2 = 0.25
        tg2 = np.arange(T / 2.0 + 10.0, T - 10.0 - dt2, dt2)
        A = np.zeros(len(tg2))
        for i, tt in enumerate(tg2):
            a = np.searchsorted(z, tt - W); b = np.searchsorted(z, tt + W)
            if a < b:
                A[i] = float(np.sum(wfun((z[a:b] - tt) * ell)))
        m = float(np.mean(A)); v = float(np.var(A))
        # C(h) 积分（h∈[0,3]，线性插值梯形）
        hs = np.array([0.0, 0.25, 0.5, 1.0, 2.0, 3.0])
        Cs = []
        for h in hs:
            kh = int(round(h / dt2))
            if kh == 0:
                Cs.append(float(np.mean((A - m) ** 2)))
            else:
                Cs.append(float(np.mean((A[:len(A) - kh] - m) * (A[kh:] - m))))
        intC = float(np.trapz(Cs, hs))
        rec = {"T": T, "ell": float(ell), "W": float(W), "N_z": int(N_z), "N_l": int(N_l),
               "N_K": int(N_K), "supSK": supSK, "mainK_at_T": float(meanN),
               "supSK_over_main": supSK / meanN,
               "supSK_over_pi_main": supSK / (np.pi * meanN),
               "mean_A": m, "var_A": v, "intC_h0_3": intC, "C_vals": Cs}
        results.append(rec)
        print("T=%6.0f  sup|S_K|=%.1f  /主项=%.2e  /(π·主项)=%.2e  ∫C(h)dh=%.4f  varA=%.4f"
              % (T, supSK, rec["supSK_over_main"], rec["supSK_over_pi_main"], intC, v))
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"results": results, "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
