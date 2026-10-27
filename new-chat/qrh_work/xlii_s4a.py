# -*- coding: utf-8 -*-
"""攻防 XLII · S4 预演：λ(T)=c(logT)^{-α} 正向构造的数值预演。
用 S2(ii) 八档数据（xlii_s2ii.json）：
  1) 固定 T 下 Δ=A−GUE2 与 GUE2−1 对 a 的幂律标度（q、2），确定 A(λ;T)−1 的主导项与符号；
  2) λ(T)=c(logT)^{-α}（α∈{1, 15/7≈2.1429, 3}，c∈{0.5,1,2}）轨迹下 A(λ;T)−1 的跨 T 衰减，
     拟合 log10(A−1) vs log10(logT) 的斜率 β，对比 β 与 15/7≈2.14、1/2（误差通道）——为 S4 定理速率定实锚。
口径：a 网格为 S2(ii) 的 {0.3,0.5,1.0,2.0}；插值用 log-log 幂律（GUE2−1）与 log-log 线性（Δ），
A(λ;T) = GUE2(λ) + Δ̂(λ;T)（Δ̂ 由 Δ(a;T) 的幂律外推）。
"""
import json, os, math
import numpy as np

QRH = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work"
OUT = os.path.join(QRH, "xlii_s4a.json")
FIG = os.path.join(QRH, "xlii_s4a_fig.png")

res = json.load(open(os.path.join(QRH, "xlii_s2ii.json"), encoding="utf-8"))
rows = res["rows"]
gue2 = res["meta"]["gue2"]
A_GRID = np.array([0.1, 0.2, 0.3, 0.5, 1.0, 2.0], dtype=float)
ALPHAS = [1.0, 15.0 / 7.0, 3.0]
CS = [0.5, 1.0, 2.0]

# ---- 1) 幂律标度 ----
# GUE2−1 vs a：期望 ~ a^2（小 a）
gkeys = list(gue2.keys())
AV = np.array([float(a) for a in gkeys], dtype=float)   # a 数值网格（升序）
la = np.log(AV)
g1 = np.array([gue2[a] - 1.0 for a in gkeys], dtype=float)
lg = np.log(g1)
kg, bg = np.polyfit(la, lg, 1)          # GUE2−1 ≈ exp(bg)·a^kg
scale = {}
for fam in ("zeta", "L"):
    qs = []
    for r_ in rows:
        A = r_["A"][fam]
        D = np.array([A[a] - gue2[a] for a in gkeys], dtype=float)
        # Δ<0：取 |Δ| 幂律，保留符号
        lD = np.log(np.abs(D))
        k, b = np.polyfit(la, lD, 1)
        qs.append((r_["T"], k, b, float(np.exp(b))))
    scale[fam] = qs

# ---- 2) λ(T) 轨迹 ----
def gue2_lamb(lmb):
    # 用 GUE2−1 ≈ exp(bg)·a^kg 外推到小 a（kg 应为 ~2）
    return 1.0 + math.exp(bg) * (lmb ** kg)

def Delta_hat(fam, T, lmb):
    # 用该 T 档的 Δ 幂律外推（Δ ≈ −exp(b)·a^k）
    for (TT, k, b, _) in scale[fam]:
        if abs(TT - T) < 1e-9:
            return -math.exp(b) * (lmb ** k)
    raise KeyError(T)

traj = {}
for fam in ("zeta", "L"):
    for alpha in ALPHAS:
        for c in CS:
            pts = []
            for r_ in rows:
                T = r_["T"]
                lmb = c / (math.log(T) ** alpha)
                A_hat = gue2_lamb(lmb) + Delta_hat(fam, T, lmb)
                pts.append({"T": T, "lambda": lmb, "A": A_hat, "A_minus_1": A_hat - 1.0})
            # 拟合 log10(A−1) vs log10(logT) 斜率 β（用 A−1>0 的点；若出现负值记符号翻转）
            TT = np.array([p["T"] for p in pts])
            Am1 = np.array([p["A_minus_1"] for p in pts])
            x = np.log10(np.log(TT)); y = np.log10(np.abs(Am1))
            ok = np.abs(Am1) > 1e-12
            kbeta, bbeta = np.polyfit(x[ok], y[ok], 1)
            sign = "pos" if np.all(Am1 > 0) else ("neg" if np.all(Am1 < 0) else "mixed")
            traj.setdefault(fam, {})["a%g_c%g" % (alpha, c)] = {
                "beta": round(float(kbeta), 4), "sign": sign,
                "pts": pts}
            print("fam=%s alpha=%.4g c=%g  beta=%.4f  sign=%s" % (fam, alpha, c, kbeta, sign), flush=True)

# ---- 汇总表 ----
summ = {}
for fam in ("zeta", "L"):
    summ[fam] = {"GUE2_power": round(float(kg), 4), "Delta_q": {}}
    for (T, k, b, e) in scale[fam]:
        summ[fam]["Delta_q"]["T%g" % T] = {"q": round(float(k), 4), "coef": round(e, 6)}
    summ[fam]["traj_beta"] = {k_: v["beta"] for k_, v in traj[fam].items()}

out = {"meta": {"alphas": ALPHAS, "cs": CS, "a_grid": A_GRID.tolist(),
                "GUE2_minus1_power_kg": round(float(kg), 4)},
       "scale": {f: [{"T": t, "q": round(q, 4), "coef": round(e, 6)} for (t, q, b, e) in scale[f]] for f in scale},
       "traj": traj, "summary": summ}
with open(OUT, "w", encoding="utf-8") as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print("saved:", OUT)

# ---- 图 ----
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
plt.rcParams["font.sans-serif"] = ["SimHei", "Microsoft YaHei"]
plt.rcParams["axes.unicode_minus"] = False
fig, axes = plt.subplots(2, 4, figsize=(18, 9))
for i, fam in enumerate(("zeta", "L")):
    ax0 = axes[i][0]
    # 左：Δ 幂律 q 跨 T
    qs = [q[1] for q in scale[fam]]
    Ts = [q[0] for q in scale[fam]]
    ax0.plot(Ts, qs, "o-", label=fam)
    ax0.axhline(2.0, color="gray", ls="--", lw=0.8)
    ax0.set_xscale("log"); ax0.set_title(fam + "  |Δ| 幂律指数 q (a^q)，参考 q=2")
    ax0.set_xlabel("T"); ax0.grid(alpha=0.3); ax0.legend()
    for j, alpha in enumerate(ALPHAS):
        ax = axes[i][1 + j]
        for c in CS:
            key = "a%g_c%g" % (alpha, c)
            pts = traj[fam][key]["pts"]
            TT = [p["T"] for p in pts]; A1 = [p["A_minus_1"] for p in pts]
            ax.plot(TT, np.abs(A1), marker="o" if c == 1 else ("s" if c == 0.5 else "^"),
                    label="c=%.1f β=%.2f" % (c, traj[fam][key]["beta"]))
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.axhline(1.0, color="gray", ls=":", lw=0.8)
        ax.set_title("%s α=%s  |A(λ;T)−1| 跨 T" % (fam, ("15/7" if abs(alpha - 15 / 7) < 1e-9 else ("1" if alpha == 1 else "3"))))
        ax.set_xlabel("T"); ax.grid(alpha=0.3); ax.legend(fontsize=8)
fig.suptitle("S4 预演：λ(T)=c(logT)^{−α} 正向构造——A(λ;T)−1 的跨 T 衰减与速率指数 β", fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.95])
fig.savefig(FIG, dpi=150)
print("fig:", FIG)
