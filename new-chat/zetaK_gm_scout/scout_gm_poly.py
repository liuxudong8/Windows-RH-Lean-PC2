# -*- coding: utf-8 -*-
"""攻防 XX 旁支侦察：并集 Dirichlet 多项式 D_K=D_zeta+D_L（系数 1+chi5(n) in {0,2}）大值分布 vs 单因子。

A 组：全 n 多项式 D(s)=sum_{n<=N} a_n n^{-it}，N=1e5，T in {N/2, N, 2N}，M=800 t 点；
B 组：素数平滑（显式公式主行、无 log 权重）P(s)=sum_{p<=X} a_p p^{-1/2} e^{-it log p}，X=1e6。
指标：归一化 sup/分位(P90/P99/P99.9)、大值频率 freq(lambda=|D|>=lambda*sqrt(M2))、经验二矩 vs 理论、并集/单族比值。
输出 JSON + 控制台表。
"""
import numpy as np, json, time, math

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\zetaK_gm_scout\scout_gm_poly.json"

def chi5(n):
    r = n % 5
    if r == 0:
        return 0
    return 1 if (r == 1 or r == 4) else -1

def eval_polys(tgrid, logn, a_list):
    """共享相位矩阵，对多个系数向量一次算完。返回 [out_i]（长度 = len(tgrid)）。"""
    M = len(tgrid)
    outs = [np.zeros(M, dtype=np.complex128) for _ in a_list]
    B = 200
    for i in range(0, M, B):
        P = np.exp(-1j * np.outer(tgrid[i:i + B], logn))
        for k, a in enumerate(a_list):
            outs[k][i:i + B] = P @ a
    return outs

def stats(z, M2t):
    q = np.percentile(z, [50, 90, 99, 99.9])
    freq = {}
    for lam in (2.0, 3.0, 4.0, 5.0):
        freq[str(lam)] = float(np.mean(z >= lam))
    return {"max": float(np.max(z)), "min": float(np.min(z)),
            "p50": float(q[0]), "p90": float(q[1]), "p99": float(q[2]), "p999": float(q[3]),
            "freq": freq, "M2_emp": float(np.mean(np.square(np.abs(z))) * M2t)}

def run():
    results = {}

    # ---------------- A: full-n Dirichlet polynomials ----------------
    N = 100_000
    n = np.arange(1, N + 1)
    logn = np.log(n)
    ch = np.array([chi5(v) for v in n], dtype=np.float64)
    aZ = np.ones(N); aL = ch; aK = 1.0 + ch
    M2 = {"zeta": float(N), "L": float(np.sum(ch * ch)), "K": float(np.sum(aK * aK))}
    Ts = [N // 2, N, 2 * N]
    Mpts = 800
    resA = {}
    for T in Ts:
        t = np.linspace(T, 2 * T, Mpts, endpoint=False)
        dZ, dL, dK = eval_polys(t, logn, (aZ, aL, aK))
        aZ2 = np.abs(dZ); aL2 = np.abs(dL); aK2 = np.abs(dK)
        out = {}
        for nm, z, m2 in (("zeta", aZ2, M2["zeta"]), ("L", aL2, M2["L"]), ("K", aK2, M2["K"])):
            out[nm] = stats(z / math.sqrt(m2), m2)
        resA[str(T)] = {
            "M2_theory": M2,
            "sup_ratio_K_over_zeta": float(np.max(aK2) / np.max(aZ2)),
            "sup_ratio_K_over_L": float(np.max(aK2) / np.max(aL2)),
            "sup_ratio_norm_K_over_zeta": float(np.max(aK2 / math.sqrt(M2["K"])) / np.max(aZ2 / math.sqrt(M2["zeta"]))),
            "p99_ratio_norm_K_over_zeta": float(np.percentile(aK2 / math.sqrt(M2["K"]), 99) / np.percentile(aZ2 / math.sqrt(M2["zeta"]), 99)),
            "polys": out,
        }
    results["A_full_n"] = {"N": N, "M_per_T": Mpts, "T_list": Ts, "detail": resA}

    # ---------------- B: prime-smoothed ----------------
    X = 1_000_000
    sieve = np.ones(X + 1, dtype=bool); sieve[:2] = False
    for i in range(2, int(X ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    pr = np.nonzero(sieve)[0].astype(np.int64)
    logp = np.log(pr)
    chp = np.array([chi5(v) for v in pr], dtype=np.float64)
    w = pr.astype(np.float64) ** (-0.5)
    bZ = w; bL = chp * w; bK = (1.0 + chp) * w
    MB2 = {"zeta": float(np.sum(bZ * bZ)), "L": float(np.sum(bL * bL)), "K": float(np.sum(bK * bK))}
    T = X
    t = np.linspace(T, 2 * T, 800, endpoint=False)
    dZ, dL, dK = eval_polys(t, logp, (bZ, bL, bK))
    aZ2 = np.abs(dZ); aL2 = np.abs(dL); aK2 = np.abs(dK)
    outB = {}
    for nm, z, m2 in (("zeta", aZ2, MB2["zeta"]), ("L", aL2, MB2["L"]), ("K", aK2, MB2["K"])):
        outB[nm] = stats(z / math.sqrt(m2), m2)
    resB = {
        "M2_theory": MB2, "X": X, "piX": int(len(pr)),
        "sup_ratio_K_over_zeta": float(np.max(aK2) / np.max(aZ2)),
        "sup_ratio_K_over_L": float(np.max(aK2) / np.max(aL2)),
        "sup_ratio_norm_K_over_zeta": float(np.max(aK2 / math.sqrt(MB2["K"])) / np.max(aZ2 / math.sqrt(MB2["zeta"]))),
        "p99_ratio_norm_K_over_zeta": float(np.percentile(aK2 / math.sqrt(MB2["K"]), 99) / np.percentile(aZ2 / math.sqrt(MB2["zeta"]), 99)),
        "polys": outB,
    }
    results["B_prime_smoothed"] = resB

    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(results, f, ensure_ascii=False, indent=1)

    print("=== A: full-n N=1e5 (T=N/2,N,2N; M=800) ===")
    for T, d in resA.items():
        print("T=%s  M2_theory zeta=%.0f L=%.0f K=%.0f" % (T, d["M2_theory"]["zeta"], d["M2_theory"]["L"], d["M2_theory"]["K"]))
        for nm in ("zeta", "L", "K"):
            st = d["polys"][nm]
            print("  %-4s max=%.3f p90=%.3f p99=%.3f p999=%.3f | freq2=%.4f freq3=%.4f freq4=%.5f | M2e/M2t=%.4f"
                  % (nm, st["max"], st["p90"], st["p99"], st["p999"], st["freq"]["2.0"], st["freq"]["3.0"], st["freq"]["4.0"], st["M2_emp"] / d["M2_theory"][nm]))
        print("  sup K/zeta=%.4f  K/L=%.4f  norm-sup K/zeta=%.4f  norm-p99 K/zeta=%.4f"
              % (d["sup_ratio_K_over_zeta"], d["sup_ratio_K_over_L"], d["sup_ratio_norm_K_over_zeta"], d["p99_ratio_norm_K_over_zeta"]))
    print("=== B: prime-smoothed X=1e6, piX=%d (T=X..2X; M=800) ===" % resB["piX"])
    for nm in ("zeta", "L", "K"):
        st = resB["polys"][nm]
        print("  %-4s max=%.3f p90=%.3f p99=%.3f p999=%.3f | freq2=%.4f freq3=%.4f | M2e/M2t=%.4f"
              % (nm, st["max"], st["p90"], st["p99"], st["p999"], st["freq"]["2.0"], st["freq"]["3.0"], st["M2_emp"] / resB["M2_theory"][nm]))
    print("  sup K/zeta=%.4f  K/L=%.4f  norm-sup K/zeta=%.4f  norm-p99 K/zeta=%.4f"
          % (resB["sup_ratio_K_over_zeta"], resB["sup_ratio_K_over_L"], resB["sup_ratio_norm_K_over_zeta"], resB["p99_ratio_norm_K_over_zeta"]))

if __name__ == "__main__":
    t0 = time.time()
    run()
    print("elapsed %.1fs" % (time.time() - t0))
