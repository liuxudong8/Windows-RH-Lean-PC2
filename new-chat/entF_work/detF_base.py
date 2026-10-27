# -*- coding: utf-8 -*-
"""S3 基线复算：Δ 常数定律（S_ζL−E）@T=6e5，对照《Delta常数定律-陈述与证据》文献数值。
口径照抄 d1_l4_work/l4_multit.py：w(u)=4/(4+u²)、λ=log T、W=R/λ、R=20、l∈[12,T−W]、ζ≤T。
输出 detF_base.json：S/E/Δ/Δ_pure（c_cut=0.0635）/Δ_pure·NK/var_A/分块。
预期对照（文献）：Δ/N_K≈−3.394%、Δ_pure≈−15091、Δ_pure/N_K≈−0.702%、var_A≈0.1144。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entF_work\detF_base.json"
T = 6.0e5
R = 20.0
C_CUT = 1.0 - 0.9365  # 0.0635：E 口径核截断修正

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
    z_full = np.sort(d["zeta"]); l_full = np.sort(d["L"])
    ell = np.log(T); W = R / ell
    z = z_full[z_full <= T]; l = l_full[l_full <= T]
    N_z, N_l = len(z), len(l); N_K = N_z + N_l
    mask = (l >= 12.0) & (l <= T - W)
    l_use = l[mask]; n_use = len(l_use)
    B = 2000
    s_parts = np.zeros(n_use)
    for i in range(0, n_use, B):
        tb = l_use[i:i + B]
        for j, tt in enumerate(tb):
            s_parts[i + j] = window_sum(z, tt, W, ell)
    S = float(np.sum(s_parts))
    E = float(np.sum(np.log(l_use / (2.0 * np.pi)) / ell))
    Delta = S - E
    Delta_pure = Delta + C_CUT * E
    blocks = []
    for i, blk in enumerate(np.array_split(l_use, 3)):
        Sb = float(np.sum(window_sum(z, tt, W, ell) for tt in blk))
        Eb = float(np.sum(np.log(blk / (2.0 * np.pi)) / ell))
        blocks.append({"i": i, "n": int(len(blk)), "S_minus_E": Sb - Eb,
                       "per_n": (Sb - Eb) / len(blk)})
    # A(t) 统计（亚泊松口径，同 l4_multit）
    dt = 0.25
    tgrid = np.arange(T / 2.0 + 10.0, T - 10.0 - dt, dt)
    A = np.zeros(len(tgrid))
    for i, tt in enumerate(tgrid):
        A[i] = window_sum(z, tt, W, ell)
    m = float(np.mean(A)); v = float(np.var(A))
    rec = {"T": T, "ell": float(ell), "W": float(W), "N_z": int(N_z), "N_l": int(N_l),
           "N_K": int(N_K), "n_use": int(n_use), "S_zetaL": S, "E": E, "Delta": Delta,
           "Delta_over_NK": Delta / N_K, "Delta_pure": Delta_pure,
           "Delta_pure_over_NK": Delta_pure / N_K,
           "Delta_pure_over_sqrtNl": Delta_pure / np.sqrt(N_l),
           "Delta_pure_over_sqrtNlvarA": Delta_pure / np.sqrt(N_l * v),
           "c_cut": C_CUT, "blocks": blocks, "mean_A": m, "var_A": v}
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(rec, f, ensure_ascii=False, indent=1)
    print("N_z=%d N_l=%d N_K=%d n_use=%d" % (N_z, N_l, N_K, n_use))
    print("S=%.1f E=%.1f Delta=%.1f Delta/NK=%.6f" % (S, E, Delta, Delta / N_K))
    print("Delta_pure=%.1f  Delta_pure/NK=%.6f  Delta_pure/sqrtNl=%.3f  /sqrt(Nl*varA)=%.3f"
          % (Delta_pure, Delta_pure / N_K, Delta_pure / np.sqrt(N_l),
             Delta_pure / np.sqrt(N_l * v)))
    print("mean_A=%.4f var_A=%.4f  blocks:" % (m, v))
    for b in blocks:
        print("  块%d: n=%d S-E=%.1f per_n=%.5f" % (b["i"], b["n"], b["S_minus_E"], b["per_n"]))
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
