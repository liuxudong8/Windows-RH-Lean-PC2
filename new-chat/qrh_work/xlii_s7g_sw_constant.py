# -*- coding: utf-8 -*-
"""攻防 XLII 数值件 G：SW 常数显式化数值定向。
ψ(X, chi5) = Σ_{n<=X} Λ(n) χ5(n)，χ5 = Legendre 符号 mod 5（n mod 5: 1,4->+1; 2,3->-1; 0->0）。
目标：实测 |ψ(X,chi5)| <= C·X·exp(-c·sqrt(log X)) 的有效 (C,c)，对照 Kadiri 理论 c~1/sqrt(6.3970)~0.395。
X 扫 1e5 -> 1e7。
"""
import json, math, time
import numpy as np

def legendre5(n):
    r = n % 5
    if r in (1, 4):
        return 1
    if r in (2, 3):
        return -1
    return 0

def sieve(N):
    isp = np.ones(N + 1, dtype=bool)
    isp[0] = isp[1] = False
    for i in range(2, int(N ** 0.5) + 1):
        if isp[i]:
            isp[i * i::i] = False
    return isp

def main():
    t0 = time.time()
    XMAX = 10_000_000
    isp = sieve(XMAX)
    primes = np.nonzero(isp)[0].tolist()
    # psi(X, chi5) = sum_{p<=X} chi5(p) log p + sum_{k>=2} sum_{p^k<=X} chi5(p^k) log p
    # chi5(p^k)=chi5(p)^k；k>=2 的素幂项：X 较小时 p^k<=1e7 的项有限
    # 直接遍历素幂
    events = []  # (n, Lambda(n)*chi5(n))
    for p in primes:
        chi = legendre5(p)
        if chi == 0:
            continue
        pk = p
        k = 1
        while pk <= XMAX:
            lp = math.log(p)
            events.append((pk, chi ** k * lp))
            pk *= p
            k += 1
    events.sort()
    # 前缀和 → psi(X, chi5)
    xs = []
    psis = []
    acc = 0.0
    idx = 0
    xs_log = np.logspace(5, 7, 41)
    for X in xs_log:
        while idx < len(events) and events[idx][0] <= X:
            acc += events[idx][1]
            idx += 1
        xs.append(float(X))
        psis.append(float(acc))
    # 拟合 |psi| <= C X exp(-c sqrt(log X))：取 log(|psi|/X) vs sqrt(log X) 线性拟合
    xs = np.array(xs)
    psis = np.array(psis)
    aps = np.abs(psis)
    valid = aps > 1e-12
    sl = np.sqrt(np.log(xs[valid]))
    y = np.log(aps[valid] / xs[valid])
    c_fit, logC_fit = np.polyfit(sl, y, 1)
    C_fit = math.exp(logC_fit)
    # 对照：理论 Kadiri c_theory = 1/sqrt(R0), R0=6.3970
    R0 = 6.3970
    c_theory = 1.0 / math.sqrt(R0)
    out = {
        "X_max": XMAX,
        "n_events": len(events),
        "xs": xs.tolist(),
        "psi": psis.tolist(),
        "abs_psi": aps.tolist(),
        "fit": {"c_eff": float(c_fit), "C_eff": float(C_fit)},
        "kadiri": {"R0": R0, "c_theory": float(c_theory)},
        "elapsed_s": time.time() - t0,
    }
    with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\xlii_s7g_sw_constant.json", "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)
    print("X=1e5..1e7, psi(X,chi5):")
    for i in range(0, len(xs), 8):
        print(f"  X={xs[i]:.3e}  psi={psis[i]:+.6e}  |psi|/X={aps[i]/xs[i]:.3e}  log(|psi|/X)={math.log(max(aps[i]/xs[i],1e-99)):.3f}  sqrt(logX)={sl[i]:.3f}")
    print(f"fit: c_eff={c_fit:.4f}  C_eff={C_fit:.3e}")
    print(f"kadiri c_theory=1/sqrt({R0})={c_theory:.4f}  elapsed={time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
