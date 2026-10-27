# -*- coding: utf-8 -*-
"""侦察 run2：T 扫描 {N^{1/2}, N^{3/4}, N, 2N} + 随机相位 Rayleigh 基线。判别 zeta/L/K tail 相对高斯基准厚度。"""
import numpy as np, json, time, math

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\zetaK_gm_scout\scout_gm_poly2.json"

def chi5(n):
    r = n % 5
    if r == 0:
        return 0
    return 1 if (r == 1 or r == 4) else -1

def eval_polys(tgrid, logn, a_list):
    M = len(tgrid)
    outs = [np.zeros(M, dtype=np.complex128) for _ in a_list]
    B = 200
    for i in range(0, M, B):
        P = np.exp(-1j * np.outer(tgrid[i:i + B], logn))
        for k, a in enumerate(a_list):
            outs[k][i:i + B] = P @ a
    return outs

def stats(z, M2t):
    q = np.percentile(z, [90, 99, 99.9])
    freq = {}
    for lam in (2.0, 3.0, 4.0):
        freq[str(lam)] = float(np.mean(z >= lam))
    return {"max": float(np.max(z)), "p90": float(q[0]), "p99": float(q[1]), "p999": float(q[2]),
            "freq": freq, "M2_emp": float(np.mean(np.square(np.abs(z))) * M2t)}

def run():
    N = 100_000
    n = np.arange(1, N + 1)
    logn = np.log(n)
    ch = np.array([chi5(v) for v in n], dtype=np.float64)
    aZ = np.ones(N); aL = ch; aK = 1.0 + ch
    M2 = {"zeta": float(N), "L": float(np.sum(ch * ch)), "K": float(np.sum(aK * aK))}
    rng = np.random.default_rng(20261019)
    aR = np.exp(1j * rng.uniform(0, 2 * np.pi, N))  # random phase baseline, same M2 as zeta
    M2["rand"] = float(np.sum(np.abs(aR) ** 2))

    Ts = [int(round(N ** 0.5)), int(round(N ** 0.75)), N, 2 * N]
    Mpts = 800
    out = {}
    for T in Ts:
        t = np.linspace(T, 2 * T, Mpts, endpoint=False)
        dZ, dL, dK, dR = eval_polys(t, logn, (aZ, aL, aK, aR))
        aZ2 = np.abs(dZ); aL2 = np.abs(dL); aK2 = np.abs(dK); aR2 = np.abs(dR)
        row = {}
        for nm, z, m2 in (("zeta", aZ2, M2["zeta"]), ("L", aL2, M2["L"]), ("K", aK2, M2["K"]), ("rand", aR2, M2["rand"])):
            row[nm] = stats(z / math.sqrt(m2), m2)
        row["M2_theory"] = M2
        out[str(T)] = row
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)

    print("=== T-scan N=1e5, M=800; Rayleigh baseline freq: lam2=0.135 lam3=0.0111 lam4=3.4e-4 ===")
    for T, row in out.items():
        print("T=%s" % T)
        for nm in ("zeta", "L", "K", "rand"):
            st = row[nm]
            print("  %-4s max=%.3f p99=%.3f | f2=%.5f f3=%.5f f4=%.5f | M2e/M2t=%.4f"
                  % (nm, st["max"], st["p99"], st["freq"]["2.0"], st["freq"]["3.0"], st["freq"]["4.0"], st["M2_emp"] / row["M2_theory"][nm]))

if __name__ == "__main__":
    t0 = time.time()
    run()
    print("elapsed %.1fs" % (time.time() - t0))
