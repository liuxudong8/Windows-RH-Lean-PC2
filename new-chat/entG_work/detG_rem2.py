# -*- coding: utf-8 -*-
"""S4 余项精细形态（第二轮）：去趋势密度余项 + 伪影斜率验证。
动机：第一轮 detG_rem 原始 sup|S_K|=3163@6e5 vs XIX 的 28.1——差异被判定为 L 数据 0.27%
R-S 求根趋势伪影（XIX §4.2：趋势 −0.0052/单位、累计 −3147@6e5）。
本件：对 S_K(t)=N_K(t)−主项_K(t) 做最小二乘线性去趋势，输出去趋势后 sup|S_K|（真实 Backlund
型量级 O(log T)）与拟合斜率 α（验证 ≈−0.0052/单位）；多 T 报告增长率。
输出 detG_rem2.json。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entG_work\detG_rem2.json"
T_LIST = [1.0e5, 2.0e5, 3.0e5, 4.0e5, 5.0e5, 6.0e5]

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z_full = np.sort(d["zeta"]); l_full = np.sort(d["L"])
    results = []
    for T in T_LIST:
        z = z_full[z_full <= T]; l = l_full[l_full <= T]
        N_z, N_l = len(z), len(l); N_K = N_z + N_l
        dt = 1.0
        tgrid = np.arange(50.0, T - 2.0, dt)
        nz = np.searchsorted(z, tgrid, side="right")
        nl = np.searchsorted(l, tgrid, side="right")
        NK = nz + nl
        mainK = (tgrid / (2.0 * np.pi)) * (2.0 * np.log(tgrid / (2.0 * np.pi)) + np.log(5.0) - 2.0) + 7.0 / 8.0
        SK = NK - mainK
        # 最小二乘去趋势：SK ~ alpha*t + beta
        A = np.vstack([tgrid, np.ones_like(tgrid)]).T
        (alpha, beta), _, _, _ = np.linalg.lstsq(A, SK, rcond=None)
        resid = SK - (alpha * tgrid + beta)
        sup_raw = float(np.max(np.abs(SK)))
        sup_det = float(np.max(np.abs(resid)))
        # 分三段 sup（检查去趋势后是否均匀）
        thirds = np.array_split(resid, 3)
        sup3 = [float(np.max(np.abs(sg))) for sg in thirds]
        rec = {"T": T, "N_z": int(N_z), "N_l": int(N_l), "N_K": int(N_K),
               "supSK_raw": sup_raw, "supSK_detrend": sup_det,
               "slope_alpha": float(alpha), "intercept_beta": float(beta),
               "sup_det_over_main": sup_det / float(mainK[-1]),
               "sup_det_per_unit_ratio": sup_det / (float(mainK[-1]) * np.pi),
               "sup_by_thirds": sup3}
        results.append(rec)
        print("T=%6.0f  sup_raw=%.0f  sup_det=%.1f  alpha=%.5f  /主项=%.2e  /(π·主项)=%.2e  三段=%.0f/%.0f/%.0f"
              % (T, sup_raw, sup_det, alpha, rec["sup_det_over_main"],
                 rec["sup_det_per_unit_ratio"], sup3[0], sup3[1], sup3[2]))
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"results": results, "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
