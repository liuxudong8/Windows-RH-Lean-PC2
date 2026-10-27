# -*- coding: utf-8 -*-
"""数值件 F：超支撑（λ→∞、核宽 a→0）素数项可忽略性实测。
检验对象：S_a(X) = Σ_{p≤X} Λ(p)χ_5(p) p^{-1/2} K̂_a(δ log p)，K̂_a(u)=K̂(a·u)。
超支撑核构造：核 f_λ(x)=λ·f₀(λx)（支撑 [−1/(2λ),1/(2λ)]，λ=1/a→∞），
频域 K̂_a(u)=∫f₀(y)cos(2π(a u/λ⁻¹ 无关)……)=K̂(a·u)（换元 y=λx，a=1/λ）。
f₀(x)=cos(√2x)/(√2 sin(1/√2))（S7 同款），δ=logT/2π。
理论判定（Abel + 点态 SW）：
  S_raw(X)=Σ_{p≤X}Λχ₅(p)p^{-1/2} = O(√X·poly(logX))；
  |S_a(X)|/N_L → 0（N_L~(X/2π)logX，X≈T 量级）——无需 e^{-c√logX} 指数级。
形态预测：f̂₀ 偶 ⟹ 一阶校正为零，K̂_a(δlogp)=1+(1/2)K̂''(0)(aδlogp)²+…
  核加权与常数核之差 δS ~ (1/2)K̂''(0)(aδ)²·ΣΛχ₅ p^{-1/2}log²p（二阶缩放 a²δ²）。
输出 xlii_s7f_supersupport.json。"""
import json, os, math
import numpy as np

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
X_MAX = 100_000_000

def sieve(n):
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if bs[i]:
            bs[i * i::i] = b"\x00" * (((n - i * i) // i) + 1)
    return np.frombuffer(bytes(bs), dtype=np.uint8)

def chi5_arr(p):
    r = p % 5
    return np.where((r == 1) | (r == 4), 1.0, -1.0)

def Khat_vec(u):
    """K̂(u)=∫_{-1/2}^{1/2} f₀(x)cos(2πux)dx（向量化）。K̂(0)=1。"""
    u = np.asarray(u, dtype=float)
    s2 = math.sqrt(2.0)
    a = s2
    b = 2 * math.pi * u
    den = s2 * math.sin(1.0 / s2)
    out = np.empty_like(b)
    nz = np.abs(b) > 1e-12
    v = np.sin((a - b[nz]) / 2) / (a - b[nz]) + np.sin((a + b[nz]) / 2) / (a + b[nz])
    out[nz] = v / den
    out[~nz] = 1.0
    return out

def N_L_approx(X):
    """零点数口径：N(T) ~ (X/2π)(log(X/2π)−1)（X≈T 量级，S6/S7 用精确计数 1.57e6@8e5）。"""
    return (X / (2 * math.pi)) * (math.log(X / (2 * math.pi)) - 1)

print("sieving to", X_MAX, "...")
flag = sieve(X_MAX)
plist = np.nonzero(flag)[0]
plist = plist[plist >= 2]
print("primes:", len(plist))
lp = np.log(plist.astype(np.float64))
w = chi5_arr(plist)
inv_sqrt = np.power(plist.astype(np.float64), -0.5)

# 未加权 SW 形态：S0(X) = Σ_{p≤X} Λχ₅ p^{-1/2}
S0 = np.cumsum(w * inv_sqrt)

# 采样点
Xs = np.unique(np.geomspace(1e4, X_MAX, 14, dtype=int))
Xs = [int(x) for x in Xs if 2 <= x <= X_MAX]

res = {"X_max": X_MAX, "N_primes": int(len(plist)),
       "Khat0": float(Khat_vec(np.array([0.0]))[0]),
       "samples": []}

# —— 主实验 A：a=1/λ=1/logT，λ=logT（超支撑档），T=X 量级 ——
for X in Xs:
    k = int(np.searchsorted(plist, X, side="right"))
    if k < 2:
        continue
    lpx = lp[:k]; wx = w[:k]; isx = inv_sqrt[:k]
    delta = math.log(X) / (2 * math.pi)          # δ=logT/2π，T=X
    a = 1.0 / math.log(X)                         # 超支撑：λ=logT → a=1/logT
    Kh = Khat_vec(a * delta * lpx)                # K̂_a(δlogp)=K̂(aδlogp)
    S_a = float(np.sum(wx * isx * Kh))
    S_raw = float(np.sum(wx * isx))
    NL = N_L_approx(X)
    res["samples"].append({
        "X": X, "delta": round(delta, 6), "a": round(a, 8), "a_delta": round(a * delta, 8),
        "S_a": round(S_a, 6), "S_raw": round(S_raw, 6),
        "|S_a|/N_L": round(abs(S_a) / NL, 8),
        "|S_a|/(√X·logX)": round(abs(S_a) / (math.sqrt(X) * math.log(X)), 6),
        "|S_raw|/(√X·logX)": round(abs(S_raw) / (math.sqrt(X) * math.log(X)), 6),
        "N_L": round(NL, 1),
    })

# —— 形态实验 B：固定 X=10^8，扫 a，验证二阶校正 δS ~ a² ——
X = X_MAX
k = len(plist)
lpx = lp; wx = w; isx = inv_sqrt
delta = math.log(X) / (2 * math.pi)
A_scan = [0.0, 1e-5, 3e-5, 1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 1e-1]
S_raw = float(np.sum(wx * isx))
T2 = float(np.sum(wx * isx * lpx * lpx))   # ΣΛχ₅ p^{-1/2} log²p（二阶校正的核）
Kpp = None
# K̂''(0) 数值：中心差分（解析可由 K̂ 展开展出）
h = 1e-4
Kpp = (Khat_vec(np.array([h]))[0] - 2.0 + Khat_vec(np.array([-h]))[0]) / (h * h)
res["form_exp"] = {"X": X, "S_raw": round(S_raw, 6), "Kpp0_numeric": round(Kpp, 4),
                   "T2": round(T2, 4), "a_scan": []}
for a in A_scan:
    if a == 0.0:
        S_a = S_raw
    else:
        Kh = Khat_vec(a * delta * lpx)
        S_a = float(np.sum(wx * isx * Kh))
    dS = S_a - S_raw
    # 预测：dS ≈ (1/2)K̂''(0)(aδ)²·T2
    pred = 0.5 * Kpp * (a * delta) ** 2 * T2 if a > 0 else 0.0
    res["form_exp"]["a_scan"].append({
        "a": a, "a_delta": round(a * delta, 8),
        "S_a": round(S_a, 6), "dS": round(dS, 6),
        "dS_pred": round(pred, 6),
        "ratio_dS_pred": round(dS / pred, 4) if abs(pred) > 1e-12 else None,
    })

with open(os.path.join(QRH, "xlii_s7f_supersupport.json"), "w", encoding="utf-8") as f:
    json.dump(res, f, indent=1, ensure_ascii=False)
print("saved xlii_s7f_supersupport.json")
for s in res["samples"][:6]:
    print("X=%-10d |S_a|/N_L=%.3e  |S_a|/(√XlogX)=%.4f  aδ=%.2e" %
          (s["X"], s["|S_a|/N_L"], s["|S_a|/(√X·logX)"], s["a_delta"]))
print("--- form_exp ---")
for s in res["form_exp"]["a_scan"]:
    print("a=%-8.1e aδ=%-9.3e  dS=%-11.6f  pred=%-11.6f  ratio=%-8s" %
          (s["a"], s["a_delta"], s["dS"], s["dS_pred"],
           ("%.3f" % s["ratio_dS_pred"]) if s["ratio_dS_pred"] is not None else "-"))
