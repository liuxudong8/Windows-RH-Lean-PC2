# -*- coding: utf-8 -*-
"""S3 注入实验：Δ 常数指纹（S_ζL−E，c_cut 修正）对"同虚部成对"离线注入的响应。
构型 I（同虚部成对，2 零点/γ）：每对在 ζ 族插 2 个零点（虚部=所选 L 零点 γ′）——w(0)=4×2=8/对。
构型 II（漏根变体，1 零点/γ）：4/对。
关键代数事实：A(t)=Σ_{γ∈ζ}w((γ−t)λ) 只依赖零点虚部——注入零点的实部（1/2±δ）对 Δ 严格无关；
窗口 |γ−t|<W=R/λ 远大于威胁带 δλ（δ≤0.01 ⇒ δλ≤0.133≪W=1.5）——满权饱和，SNR 不随 δ 衰减。
增量法：ΔS_inj=Σ_{γ_i}Σ_{l′∈l_use,|l′−γ_i|<W} w((γ_i−l′)λ)（A 对 z 线性，精确）；一次全量重算验证。
SNR 噪声口径：σ_A=√(N_l·var_A)（实测 362.6）与 σ_√Nl=√N_l（1072.5）双报。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entF_work\detF_inject.json"
T = 6.0e5
R = 20.0
C_CUT = 0.0635
SEED0 = 20261024

def wfun(u):
    return 4.0 / (4.0 + u * u)

def window_sum(roots, t, W, ell):
    lo = np.searchsorted(roots, t - W)
    hi = np.searchsorted(roots, t + W)
    if lo >= hi:
        return 0.0
    return float(np.sum(wfun((roots[lo:hi] - t) * ell)))

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z_full = np.sort(d["zeta"]); l_full = np.sort(d["L"])
    ell = np.log(T); W = R / ell
    z = z_full[z_full <= T]; l = l_full[l_full <= T]
    N_z, N_l = len(z), len(l); N_K = N_z + N_l
    mask = (l >= 12.0) & (l <= T - W)
    l_use = l[mask]; n_use = len(l_use)
    # 基线（复用 base 数值，全量重算保一致）
    B = 2000
    s_parts = np.zeros(n_use)
    for i in range(0, n_use, B):
        tb = l_use[i:i + B]
        for j, tt in enumerate(tb):
            s_parts[i + j] = window_sum(z, tt, W, ell)
    S0 = float(np.sum(s_parts))
    E = float(np.sum(np.log(l_use / (2.0 * np.pi)) / ell))
    D0 = S0 - E
    DP0 = D0 + C_CUT * E
    var_A = 0.1144
    sigA = float(np.sqrt(N_l * var_A))
    sigN = float(np.sqrt(N_l))
    print("baseline S0=%.1f D0=%.1f DP0=%.1f sigA=%.1f sigN=%.1f" % (S0, D0, DP0, sigA, sigN))

    def delta_S_inj(gamma_list):
        g = np.asarray(gamma_list)
        lo = np.searchsorted(l_use, g - W)
        hi = np.searchsorted(l_use, g + W)
        tot = 0.0
        for i in range(len(g)):
            a, b = lo[i], hi[i]
            if a < b:
                tot += float(np.sum(wfun((l_use[a:b] - g[i]) * ell)))
        return tot

    n_pairs_list = [100, 200, 2000, 219000]
    reps = 5
    rng = np.random.default_rng(SEED0)
    results = {"T": T, "ell": float(ell), "W": float(W), "N_z": int(N_z), "N_l": int(N_l),
               "N_K": int(N_K), "n_use": int(n_use), "S0": S0, "E": E, "D0": D0, "DP0": DP0,
               "sigA": sigA, "sigN": sigN, "var_A": var_A, "C_CUT": C_CUT,
               "injections": []}
    for np_ in n_pairs_list:
        for conf, mult in [("I_pair2", 2), ("II_single1", 1)]:
            dS_arr = []
            for r in range(reps):
                idx = rng.choice(n_use, size=np_, replace=False)
                gamma = l_use[idx]
                gamma_list = np.repeat(gamma, mult)  # I: 每对 2 个同虚部零点；II: 1 个
                dS_arr.append(delta_S_inj(gamma_list))
            dS = np.mean(dS_arr); dS_std = np.std(dS_arr)
            DP = DP0 + dS
            rec = {"n_pairs": int(np_), "config": conf, "mult": int(mult),
                   "dS_mean": float(dS), "dS_std": float(dS_std),
                   "SNR_sigA": float(dS / sigA), "SNR_sigN": float(dS / sigN),
                   "DP_inj": float(DP), "DP_inj_over_NK": float(DP / N_K),
                   "rel_shift_of_absDP": float(dS / abs(DP0))}
            results["injections"].append(rec)
            print("np=%6d %s  dS=%.1f±%.1f  SNR(sigA)=%.2f  SNR(sigN)=%.2f  DP/NK=%.6f  dS/|DP0|=%.3f"
                  % (np_, conf, dS, dS_std, rec["SNR_sigA"], rec["SNR_sigN"],
                     rec["DP_inj_over_NK"], rec["rel_shift_of_absDP"]))
    # 全量重算验证：n=219000 构型 I（插 438000 零点后完整重算 S）
    np_ = 219000
    rng2 = np.random.default_rng(SEED0 + 7)
    idx = rng2.choice(n_use, size=np_, replace=False)
    gamma = l_use[idx]
    gamma_list = np.repeat(gamma, 2)
    z_inj = np.sort(np.concatenate([z, gamma_list]))
    s_parts2 = np.zeros(n_use)
    for i in range(0, n_use, B):
        tb = l_use[i:i + B]
        for j, tt in enumerate(tb):
            s_parts2[i + j] = window_sum(z_inj, tt, W, ell)
    S_inj = float(np.sum(s_parts2))
    dS_full = S_inj - S0
    dS_inc = delta_S_inj(gamma_list)
    results["fullcheck"] = {"n_pairs": np_, "config": "I_pair2", "S_inj": S_inj,
                            "dS_full": dS_full, "dS_incremental": dS_inc,
                            "rel_diff": abs(dS_full - dS_inc) / abs(dS_inc)}
    print("FULLCHECK np=219000 I: dS_full=%.1f dS_incremental=%.1f rel_diff=%.2e"
          % (dS_full, dS_inc, results["fullcheck"]["rel_diff"]))
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(results, f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
