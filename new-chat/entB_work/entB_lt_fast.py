# -*- coding: utf-8 -*-
"""左尾 224 审计·快速定向：两族求根质量对照（秒级，免重跑峰高）。

问题：B4 左尾 ĥ<3 为 ζ 216 / L 8，与攻防 XIX「L 族 0.27% R-S 漏根伪影（−3147 个）」方向相反。
快速定向：测 ζ 族与 L 族的求根结构签名——间距分布（漏根⟹大间距异常；假根⟹极近对）、
计数剖面趋势（XIX 的 −0.0052/单位 是否在 ζ 族也存在）、重复/极近对（重根判定）。
"""
import numpy as np, json, math

z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
Zz = np.sort(z["zeta"]); ZL = np.sort(z["L"])
T = 6e5

def fam_stats(g, name):
    d = np.diff(g)
    out = dict(
        name=name, n=int(len(g)),
        d_min=float(d.min()), d_p1=float(np.percentile(d, 1)),
        d_p50=float(np.percentile(d, 50)), d_p99=float(np.percentile(d, 99)),
        d_max=float(d.max()),
        # 极近对（<1e-4：重复/假根嫌疑）与异常大间距（>10×中位：漏根嫌疑）
        n_close= int(np.sum(d < 1e-4)), n_close_1e3= int(np.sum(d < 1e-3)),
        n_wide_10x= int(np.sum(d > 10 * np.median(d))),
        n_wide_5x= int(np.sum(d > 5 * np.median(d))),
        # 计数剖面趋势：每 6e4 段零点数与理论 (T/2π)log 主项偏差
    )
    # 段计数 vs 理论（ζ: (T/2π)log(T/2π)；L: (T/2π)[log(T/2π)+log5−1]）
    lam = math.log(T / (2 * math.pi))
    edges = np.arange(0, T + 1, 6e4)
    hist, _ = np.histogram(g, bins=edges)
    es = np.maximum(edges, 1.0)
    theo_zeta = (es / (2*math.pi)) * (np.log(es/(2*math.pi)) - 1)
    theo_L = (es / (2*math.pi)) * (np.log(es/(2*math.pi)) + math.log(5) - 1)
    dev_zeta = (hist - np.diff(theo_zeta))
    dev_L = (hist - np.diff(theo_L))
    out["seg_dev_mean"] = float(dev_zeta.mean()) if name == "zeta" else float(dev_L.mean())
    out["seg_dev_max"] = float(dev_zeta.max()) if name == "zeta" else float(dev_L.max())
    out["seg_dev_sum"] = float(dev_zeta.sum()) if name == "zeta" else float(dev_L.sum())
    out["n_seg"] = int(len(hist))
    return out

res = {"T": T,
       "zeta": fam_stats(Zz, "zeta"),
       "L": fam_stats(ZL, "L")}
# 全局极近对（跨族重复）
G = np.sort(np.concatenate([Zz, ZL]))
dG = np.diff(G)
res["union_n_close_1e-4"] = int(np.sum(dG < 1e-4))
res["union_n_close_1e-6"] = int(np.sum(dG < 1e-6))
print(json.dumps(res, ensure_ascii=False, indent=1))
with open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_lt_fast.json", "w", encoding="utf-8") as fp:
    json.dump(res, fp, ensure_ascii=False, indent=1)
print("SAVED entB_work/entB_lt_fast.json")
