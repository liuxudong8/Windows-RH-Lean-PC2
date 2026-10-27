# -*- coding: utf-8 -*-
"""S4/XL 配对偏差显著性判定：配对侧余项是"系统偏离"还是"随机涨落"？
文献事实（2609.02882v2 Lemma 3.1=BGS 无条件配对公式）：配对和误差 O_f(1/√logT)≈0.27@6e5——
定理界。本件判定数值偏差的量级归属：
(i) ∫C(h)dh 的统计显著性（SE 传播：C(h) 各点 SE≈C(0)·√(2/Neff)，Neff=A 网格有效独立样本）；
(ii) 偏差与 1/√N_K（拟随机涨落尺度）对照；
(iii) 偏差与 1/√logT（定理界尺度）对照——判定"配对和=主项+随机涨落"还是"系统偏离"。
输入：detG_rem.json（多 T 的 C_vals、var_A、N_K）。输出 detG_pc.json。"""
import numpy as np, json

INP = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entG_work\detG_rem.json"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entG_work\detG_pc.json"

def main():
    with open(INP, encoding="utf-8") as f:
        data = json.load(f)
    hs = np.array([0.0, 0.25, 0.5, 1.0, 2.0, 3.0])
    res = []
    for r in data["results"]:
        T = r["T"]; N = r["N_K"]
        ell = np.log(T)
        C = np.array(r["C_vals"]); varA = r["var_A"]
        # A 网格点数（detG_rem 口径：tg2 从 T/2+10 到 T-10，dt2=0.25）
        n_grid = int((T - 10.0 - (T / 2.0 + 10.0)) / 0.25)
        # 有效独立样本：相关长度 ~ W（窗口宽度 W=20/ell），Neff = n_grid * dt2 / W
        W = 20.0 / ell
        neff = n_grid * 0.25 / W
        # C(h) 各点 SE：C(h) 是 (A-m)(A_{h}-m) 的均值，方差 ~ 2*varA^2/Neff（乘积矩传播）
        se_c = np.sqrt(2.0) * varA / np.sqrt(neff)
        # ∫C 的 SE：梯形积分，h 步长不等（0.25,0.25,0.25,0.5,1.0）——按权重传播
        # 梯形权: 首尾 0.5*Δh，中间 Δh
        dhs = np.diff(hs)
        wts = np.concatenate([[0.5 * dhs[0]], 0.5 * (dhs[:-1] + dhs[1:]), [0.5 * dhs[-1]]])
        intC = float(np.sum(wts * C))
        se_int = float(np.sqrt(np.sum((wts * se_c) ** 2)))
        z_int = intC / se_int if se_int > 0 else float("nan")
        rec = {"T": T, "N_K": N, "ell": float(ell), "n_grid": n_grid, "neff": float(neff),
               "W": float(W), "var_A": varA, "intC": intC, "se_int": se_int, "z_int": z_int,
               "one_over_sqrt_N": 1.0 / np.sqrt(N), "one_over_sqrt_log": 1.0 / np.sqrt(ell),
               "one_over_log": 1.0 / ell, "C_vals": r["C_vals"]}
        res.append(rec)
        print("T=%6.0f  ∫C=%.5f  SE=%.5f  z=%.2fσ  1/√N=%.1e  1/√logT=%.3f  1/logT=%.3f"
              % (T, intC, se_int, z_int, rec["one_over_sqrt_N"], rec["one_over_sqrt_log"], rec["one_over_log"]))
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"results": res, "hs": hs.tolist(), "method": "SE via 2*varA^2/Neff product-moment propagation"},
                  f, ensure_ascii=False, indent=1)
    print("saved", OUT)

if __name__ == "__main__":
    main()
