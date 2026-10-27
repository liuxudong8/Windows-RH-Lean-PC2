# -*- coding: utf-8 -*-
"""QRH 攻坚 · 数值定向 #4：并集最近邻统计 vs 独立 GUE 混合模拟。
audit3 判定：换族 0.753 = 独立 GUE 混合自然值（z=-1.1σ）。补并集最近邻对照：
实测并集 NN（归一化均值 1）：var=0.4405、p(0+)=0.540、s-exp=0.01。
本件：独立 GUE 混合模拟（R 次）输出并集 NN 的 var/p(0+)/s-exp 分布——判定并集统计是否完全由
"两族独立 GUE"决定（若是 → 拟随机前提在并集最近邻层也数值成立；若实测显著偏离 → 需额外机制）。
同时输出模拟的跨族最近邻 mean（对照实测 0.272）。输出 qrh_audit4.json。"""
import numpy as np, json, time

NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\qrh_work\qrh_audit4.json"
T = 6.0e5
LOW = 300.0
R = 30

def rho_zeta(t):
    return np.log(t / (2.0 * np.pi)) / (2.0 * np.pi)

def rho_L(t):
    return (np.log(t / (2.0 * np.pi)) + np.log(5.0) - 1.0) / (2.0 * np.pi)

def nn_stats_full(tt, kind):
    """并集最近邻统计 + 换族 + 跨族最近邻。tt 已排序、kind 族标。"""
    dt = np.diff(tt)
    nn = np.minimum(dt, np.concatenate([[np.inf], dt[:-1]]))
    mid = (tt[:-1] + tt[1:]) / 2.0
    rho_u = rho_zeta(mid) + rho_L(mid)
    s_u = nn * rho_u
    s_u1 = s_u / s_u.mean()
    var = float(s_u1.var()); mean1 = float(s_u1.mean())
    small = s_u1[s_u1 < 0.1]
    p0 = float(len(small) / len(s_u1) / 0.1) if len(s_u1) else float("nan")
    ss = s_u1[s_u1 < 0.3]
    if len(ss) > 20:
        bc = np.bincount(np.clip((ss / 0.005).astype(int), 0, 59), minlength=60)[0:60]
        xb = (np.arange(60) + 0.5) * 0.005
        m = bc > 0
        sexp = float(np.polyfit(np.log(xb[m]), np.log(bc[m]), 1)[0])
    else:
        sexp = float("nan")
    flips = float(np.sum(kind[1:] != kind[:-1])) / (len(kind) - 1)
    # 跨族最近邻（ζ→L，L 密度归一化）
    z = tt[kind == 0]; l = tt[kind == 1]
    idx = np.searchsorted(l, z, side="right"); idx = np.clip(idx, 1, len(l) - 1)
    dL = np.minimum(np.abs(l[idx] - z), np.abs(l[idx - 1] - z))
    sc = dL * rho_L(z)
    return {"var": var, "mean": mean1, "p0plus": p0, "sexp": sexp,
            "flip": flips, "cross_mean": float(sc.mean()), "cross_var": float(sc.var())}

def rebuild(orig, start, stop):
    gaps = np.diff(orig)
    if len(gaps) < 1:
        return np.array([])
    k = np.random.randint(0, len(gaps))
    gaps = np.roll(gaps, k)
    t = start; out = []
    for g in gaps:
        t = t + g
        if t >= stop:
            break
        out.append(t)
    return np.array(out)

def main():
    t0 = time.time()
    d = np.load(NPZ)
    z = np.sort(d["zeta"]); l = np.sort(d["L"])
    z = z[(z >= LOW) & (z <= T)]; l = l[(l >= LOW) & (l <= T)]
    zz = np.stack([z, np.zeros(len(z))], 1); ll = np.stack([l, np.ones(len(l))], 1)
    allz = np.concatenate([zz, ll]); allz = allz[np.argsort(allz[:, 0])]
    obs = nn_stats_full(allz[:, 0], allz[:, 1])
    print("实测：var=%.4f p0=%.3f sexp=%.2f flip=%.4f cross_mean=%.4f cross_var=%.4f"
          % (obs["var"], obs["p0plus"], obs["sexp"], obs["flip"], obs["cross_mean"], obs["cross_var"]))
    sims = {"var": [], "p0plus": [], "sexp": [], "flip": [], "cross_mean": [], "cross_var": []}
    for r in range(R):
        zr = rebuild(z, LOW, T)
        lr = rebuild(l, LOW, T)
        zz2 = np.stack([zr, np.zeros(len(zr))], 1); ll2 = np.stack([lr, np.ones(len(lr))], 1)
        a2 = np.concatenate([zz2, ll2]); a2 = a2[np.argsort(a2[:, 0])]
        s = nn_stats_full(a2[:, 0], a2[:, 1])
        for kk in sims:
            sims[kk].append(s[kk])
    print("模拟独立 GUE 混合（R=%d）：" % R)
    for kk in ["var", "p0plus", "sexp", "flip", "cross_mean", "cross_var"]:
        arr = np.array(sims[kk])
        zs = (obs[kk] - arr.mean()) / (arr.std() + 1e-12)
        print("  %-11s obs=%.4f  sim mean=%.4f±%.4f  z=%.1fσ" % (kk, obs[kk], arr.mean(), arr.std(), zs))
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"observed": obs, "sim": {k: {"mean": float(np.mean(v)),
                 "std": float(np.std(v)), "z": float((obs[k] - np.mean(v)) / (np.std(v) + 1e-12))}
                 for k, v in sims.items()}, "R": R, "elapsed": time.time() - t0},
                 f, ensure_ascii=False, indent=1)
    print("saved", OUT, "elapsed %.1fs" % (time.time() - t0))

if __name__ == "__main__":
    main()
