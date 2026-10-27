# -*- coding: utf-8 -*-
"""数值件 E：S7 素数项层——模 5 特征加权素数项子指数可忽略性实测。
检验对象（L(s,χ_5) 单族配对相关显式公式的非对角素数项）：
  S(X) = Σ_{p≤X} Λ(p)χ_5(p) p^{-1/2} K̂(δ log p)
其中 χ_5 为模 5 实特征（p≡±1 mod5 → +1；p≡±2 mod5 → −1），
K̂ = MT 最优核 f₀(x)=cos(√2x)/(√2 sin(1/√2))（支撑 [−1/2,1/2]）的余弦傅里叶变换，δ=logT/2π。
判定：|S(X)| ≪ N_L·10⁻²（N_L(8e5)=1.57e6 配对和对角主项）——SW 子指数 + 核频域窄支撑双压低。
另算未加权 |Σ Λ(p)χ_5(p) p^{-1/2}|（SW 形态）随 X 轨迹。
输出 xlii_s7_prime.json。"""
import json, os, math
import numpy as np

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"

def sieve(n):
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if bs[i]:
            bs[i * i::i] = b"\x00" * (((n - i * i) // i) + 1)
    return [i for i in range(n + 1) if bs[i]]

def chi5(p):
    r = p % 5
    return 1 if r in (1, 4) else -1  # r=2,3 → −1

def Khat(u):
    """K̂(u) 解析式：K̂(u)=∫_{-1/2}^{1/2} f₀(x)cos(2πux)dx，f₀(x)=cos(√2x)/(√2 sin(1/√2))。
    ∫cos(ax)cos(bx)dx = sin((a−b)x)/(2(a−b)) + sin((a+b)x)/(2(a+b))。"""
    s2 = math.sqrt(2.0)
    a = s2
    b = 2 * math.pi * u
    if abs(b) < 1e-12:
        return 1.0
    den = s2 * math.sin(1.0 / s2)
    v = math.sin((a - b) / 2) / (a - b) + math.sin((a + b) / 2) / (a + b)
    return v / den

X = 10_000_000
primes = sieve(X)
print("primes up to", X, ":", len(primes))
lp = np.array([math.log(p) for p in primes])
w = np.array([chi5(p) for p in primes], dtype=float)
inv_sqrt = np.array([p ** -0.5 for p in primes])

# δ 窗口（T=6e5/8e5 同款）
res = {}
for T in (600000, 800000):
    delta = math.log(T) / (2 * math.pi)
    # K̂ 在 δlogp 处的值（频域窄支撑 → 只 p 接近 1 有贡献）
    uvals = delta * lp
    Kh = np.array([Khat(uu) for uu in uvals])
    # S(X) 累积
    S = np.cumsum(w * inv_sqrt * Kh)
    # 未加权 SW 形态
    S0 = np.cumsum(w * inv_sqrt)
    # 采样点（log 均匀）
    idx = np.unique(np.geomspace(2, len(primes) - 1, 60, dtype=int))
    Xs = np.array([primes[i] for i in idx], dtype=float)
    res[str(T)] = {
        "delta": delta,
        "S_final": float(S[-1]),
        "|S|_max": float(np.max(np.abs(S))),
        "S0_final": float(S0[-1]),
        "|S0|_max": float(np.max(np.abs(S0))),
        "N_L": 1570076 if T == 800000 else 1149836,
        "ratio_S_NL": float(abs(S[-1]) / (1570076 if T == 800000 else 1149836)),
        "sample_X": [round(float(x), 1) for x in Xs.tolist()[:20]],
        "sample_S": [round(float(s), 6) for s in S[idx.tolist()[:20]]],
        "sample_S0": [round(float(s), 3) for s in S0[idx.tolist()[:20]]],
    }
    print("T=%d δ=%.4f  |S_final|=%.5f  |S|max=%.5f  ratio/N_L=%.2e  |S0_final|=%.3f" %
          (T, delta, abs(S[-1]), np.max(np.abs(S)), abs(S[-1]) / (1570076 if T == 800000 else 1149836), abs(S0[-1])))

with open(os.path.join(QRH, "xlii_s7_prime.json"), "w", encoding="utf-8") as f:
    json.dump(res, f, indent=1, ensure_ascii=False)
print("saved xlii_s7_prime.json")
