# -*- coding: utf-8 -*-
"""多 T 稳定性扫描：Delta=S_zetaL-E 随 T 截断的收敛（T'=1e5..6e5，R=20 固定口径）。
输出 l4_multit.json：每 T' 的 S/E/Delta/Delta_NK/分块/A 统计/C(h)。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\d1_l4_work\l4_multit.json"

def wfun(u):
    return 4.0 / (4.0 + u * u)

def window_sum(roots, t, W, ell):
    lo = np.searchsorted(roots, t - W)
    hi = np.searchsorted(roots, t + W)
    if lo >= hi:
        return 0.0
    u = (roots[lo:hi] - t) * ell
    return float(np.sum(wfun(u)))

def run_T(z_full, l_full, T, R=20.0):
    ell = np.log(T); W = R / ell
    z = z_full[z_full <= T]; l = l_full[l_full <= T]
    N_z, N_l = len(z), len(l); N_K = N_z + N_l
    lo_b, hi_b = 12.0, T - W
    mask = (l >= lo_b) & (l <= hi_b)
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
    sig_ref = float(np.sqrt(N_l))
    blocks = []
    for i, blk in enumerate(np.array_split(l_use, 3)):
        Sb = float(np.sum(window_sum(z, tt, W, ell) for tt in blk))
        Eb = float(np.sum(np.log(blk / (2.0 * np.pi)) / ell))
        blocks.append({"i": i, "n": int(len(blk)), "S_minus_E": Sb - Eb,
                       "per_n": (Sb - Eb) / len(blk)})
    dt = 0.25
    tgrid = np.arange(T / 2.0 + 10.0, T - 10.0 - dt, dt)
    A = np.zeros(len(tgrid))
    for i, tt in enumerate(tgrid):
        A[i] = window_sum(z, tt, W, ell)
    m = float(np.mean(A)); v = float(np.var(A))
    corr = []
    for h in [0.0, 0.25, 0.5, 1.0, 2.0]:
        kh = int(round(h / dt))
        if kh == 0:
            c = float(np.mean((A - m) ** 2))
        else:
            c = float(np.mean((A[:len(A) - kh] - m) * (A[kh:] - m)))
        corr.append({"h": h, "C": c})
    return {"T": T, "ell": float(ell), "W": float(W), "N_z": int(N_z), "N_l": int(N_l),
            "N_K": int(N_K), "n_use": int(n_use), "S_zetaL": S, "E": E, "Delta": Delta,
            "Delta_over_NK": Delta / N_K, "Delta_over_sqrtNl": Delta / sig_ref,
            "blocks": blocks, "mean_A": m, "var_A": v, "C_zeta": corr}

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z_full = np.sort(d["zeta"]); l_full = np.sort(d["L"])
    results = []
    for T in [1.0e5, 2.0e5, 3.0e5, 4.0e5, 5.0e5, 6.0e5]:
        rec = run_T(z_full, l_full, T)
        results.append(rec)
        print("T=%6.0f  ell=%.4f W=%.4f  N_z=%d N_l=%d N_K=%d n_use=%d  "
              "Delta=%.1f  Delta/N_K=%.6f  Delta/sqrtNl=%.3f  meanA=%.4f varA=%.4f"
              % (T, rec["ell"], rec["W"], rec["N_z"], rec["N_l"], rec["N_K"], rec["n_use"],
                 rec["Delta"], rec["Delta_over_NK"], rec["Delta_over_sqrtNl"],
                 rec["mean_A"], rec["var_A"]))
        for b in rec["blocks"]:
            print("   块%d: n=%d  S-E=%.1f  per_n=%.5f" % (b["i"], b["n"], b["S_minus_E"], b["per_n"]))
        print("   C(h): " + " ".join("h=%.2f->%.5f" % (c["h"], c["C"]) for c in rec["C_zeta"]))
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"T_list": [r["T"] for r in results], "results": results,
                   "elapsed": time.time() - t0}, f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
