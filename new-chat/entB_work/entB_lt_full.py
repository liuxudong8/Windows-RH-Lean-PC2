# -*- coding: utf-8 -*-
"""左尾 224 审计·v3（~50 分钟）：峰高重跑（口径同 B4，Part1 结果落盘 h_full.npy 可复用）
+ Part3 在线判定优先（dps=8，每点 1 次 zetaK 在线判定；仅非在线点做粗扫+精化 σ 扫描）。

Part1：与 entB_full.py 逐行一致（EPS=0.1、DT_BG=0.2、D_CUT=5、掩码 |d|>1e-6、CHUNK=5000、BLK=20000）。
若 entB_work/h_full.npy 存在（此前已算），跳过 Part1 直接读取（h + G + maskZ 打包存 npyz）。
"""
import numpy as np, json, time, math, os

t0 = time.time()
T = 6e5; X = 300_000
EPS = 0.1; DT_BG = 0.2; D_CUT = 5.0
BASE = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work"
H_NPZ = os.path.join(BASE, "h_full.npz")

def log(msg):
    print(msg, flush=True)

z = np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")
Zz = np.sort(z["zeta"]); ZL = np.sort(z["L"])
G = np.sort(np.concatenate([Zz, ZL])); N_K = len(G)

if os.path.exists(H_NPZ):
    d = np.load(H_NPZ)
    h, maskZ = d["h"], d["maskZ"]
    log("复用 h_full.npz（n=%d）" % len(h))
else:
    def sieve(n):
        s = np.ones(n+1, dtype=bool); s[:2] = False
        for i in range(2, int(n**0.5)+1):
            if s[i]: s[i*i::i] = False
        return np.nonzero(s)[0]
    ps = sieve(X)
    chi5 = np.where(ps % 5 == 0, 0, np.where((ps % 5 == 1) | (ps % 5 == 4), 1, -1))
    a1 = (1.0 + chi5) * np.log(ps) / np.sqrt(ps) * np.exp(-EPS * np.log(ps))
    lp = np.log(ps); Np = len(ps)
    log("Part1 背景粗网格…")
    tg = np.arange(0.0, T + DT_BG, DT_BG); ng = len(tg)
    bg = np.empty(ng, dtype=np.float64)
    CHUNK = 5000
    for i0 in range(0, ng, CHUNK):
        tb = tg[i0:i0+CHUNK]
        bg[i0:i0+len(tb)] = np.real(a1 @ np.exp(-1j * np.outer(lp, tb)))
    bg_at = np.interp(G, tg, bg)
    log("Part1 背景完成 %.0fs；峰叠加…" % (time.time()-t0))
    idx_lo = np.searchsorted(G, G - D_CUT)
    idx_hi = np.searchsorted(G, G + D_CUT)
    peaks = np.full(N_K, 1.0/EPS, dtype=np.float64)
    BLK = 20000
    for i0 in range(0, N_K, BLK):
        i1 = min(i0 + BLK, N_K)
        seg = G[i0:i1]
        lo = idx_lo[i0:i1].min(); hi = idx_hi[i1-1].max()
        gsub = G[lo:hi]
        d = gsub.reshape(1, -1) - seg.reshape(-1, 1)
        m = (np.abs(d) <= D_CUT) & (np.abs(d) > 1e-6)
        peaks[i0:i1] += np.where(m, EPS/(EPS*EPS + d*d), 0.0).sum(axis=1)
    h = bg_at + peaks
    maskZ = np.isin(G, Zz)
    np.savez(H_NPZ, h=h, maskZ=maskZ)
    log("Part1 峰高完成 %.0fs；已存 h_full.npz" % (time.time()-t0))

log("并集 mean=%.4f std=%.4f | ζ mean=%.4f std=%.4f | L mean=%.4f std=%.4f"
    % (h.mean(), h.std(ddof=1), h[maskZ].mean(), h[maskZ].std(ddof=1), h[~maskZ].mean(), h[~maskZ].std(ddof=1)))
lt3 = np.where(h < 3.0)[0]
lt1 = np.where(h < 1.0)[0]
log("左尾 ĥ<3: %d（ζ %d / L %d）；ĥ<1: %d" % (len(lt3), np.isin(G[lt3], Zz).sum(), np.isin(G[lt3], ZL).sum(), len(lt1)))

dG = np.diff(G)
detail = []
for i in np.concatenate([lt3, lt1]):
    g = G[i]
    nn = dG[min(max(0, i-1), len(dG)-1)]
    if i > 0 and i < len(G):
        nn = min(dG[i-1], dG[i])
    detail.append(dict(gamma=float(g), h=float(h[i]), fam="zeta" if maskZ[i] else "L",
                       nn=float(nn), lt1=bool(h[i] < 1.0)))
log("左尾明细 %d 条" % len(detail))

# ---------- Part3 在线判定优先（dps=8） ----------
import mpmath as m
m.mp.dps = 8

def zetaK(s):
    chi5_v = [1, -1, -1, 1]
    L = m.power(5, -s) * sum(m.zeta(s, a/5.0) * cv for a, cv in enumerate(chi5_v, start=1))
    return m.zeta(s) * L

def scan_offline(g):
    """非在线点：粗扫 0.02 → 局部精化 0.002。返回 (smin, mmin, mhalf)。"""
    coarse = np.arange(0.30, 0.7001, 0.02)
    vals = [float(abs(zetaK(m.mpc(s, g)))) for s in coarse]
    k = int(np.argmin(vals))
    s0 = coarse[max(0, k-1)]; s1 = coarse[min(len(coarse)-1, k+1)]
    fine = np.arange(s0, s1 + 1e-9, 0.002)
    vf = [float(abs(zetaK(m.mpc(s, g)))) for s in fine]
    j = int(np.argmin(vf))
    mhalf = float(abs(zetaK(m.mpc(0.5, g))))
    return float(fine[j]), float(vf[j]), mhalf

ON_TH = 1e-2   # 在线判定阈值：|ζ_K(0.5+iγ)| < 1e-2 视为在线（真零点处模≈0）
meas = []
for it, rec in enumerate(detail):
    g = rec["gamma"]
    mhalf = float(abs(zetaK(m.mpc(0.5, g))))
    if mhalf < ON_TH:
        rec["smin"] = 0.5; rec["mmin"] = mhalf; rec["mhalf"] = mhalf
        rec["has_zero"] = True; rec["delta"] = 0.0; rec["mpair"] = None
        rec["mode"] = "online"
    else:
        smin, mmin, mhalf2 = scan_offline(g)
        bg_ref = max(mhalf2, 1e-30)
        has_zero = (mmin < ON_TH) and (mmin < 0.5 * bg_ref)
        delta = max(0.0, 0.5 - smin) if has_zero else None
        rec["smin"] = smin; rec["mmin"] = mmin; rec["mhalf"] = mhalf2
        rec["has_zero"] = bool(has_zero); rec["delta"] = delta
        if has_zero and delta is not None and delta > 0.01:
            v2 = zetaK(m.mpc(1.0 - smin, g))
            rec["mpair"] = float(abs(v2))
            rec["mode"] = "offline_pair"
        elif has_zero:
            rec["mpair"] = None
            rec["mode"] = "offline_shallow"
        else:
            rec["mpair"] = None
            rec["mode"] = "fake"
    meas.append(rec)
    if (it+1) % 50 == 0 or it == len(detail)-1:
        log("Part3 测量 %d/%d（%.0fs）" % (it+1, len(detail), time.time()-t0))
        json.dump(dict(partial=True, n_done=it+1, items=meas),
                  open(os.path.join(BASE, "entB_lt_partial.json"), "w", encoding="utf-8"),
                  ensure_ascii=False, indent=1)

n_z = sum(1 for r in meas if r["has_zero"])
n_fake = len(meas) - n_z
n_off = sum(1 for r in meas if (r["has_zero"] and r["delta"] is not None and r["delta"] > 0.01))
n_on = n_z - n_off
deltas = sorted([r["delta"] for r in meas if r["has_zero"] and r["delta"] is not None and r["delta"] > 0])
mpair_small = sum(1 for r in meas if r["mpair"] is not None and r["mpair"] < ON_TH)

summary = dict(n_left=len(meas), n_zeta=sum(1 for r in meas if r["fam"]=="zeta"),
               n_L=sum(1 for r in meas if r["fam"]=="L"),
               n_has_zero=n_z, n_fake=n_fake, n_off_gt0_01=n_off, n_on=n_on,
               delta_min=float(min(deltas)) if deltas else None,
               delta_max=float(max(deltas)) if deltas else None,
               delta_median=float(np.median(deltas)) if deltas else None,
               n_pair_confirmed=mpair_small, runtime_s=time.time()-t0)
out = dict(summary=summary, items=meas)
with open(os.path.join(BASE, "entB_lt_full.json"), "w", encoding="utf-8") as fp:
    json.dump(out, fp, ensure_ascii=False, indent=1)
log("=== 汇总 ===")
log("左尾 %d（ζ %d / L %d）；有零点 %d；假根 %d；离线(δ>0.01) %d；在线 %d；配对确认 %d"
    % (summary["n_left"], summary["n_zeta"], summary["n_L"], n_z, n_fake, n_off, n_on, mpair_small))
log("δ 分布：min %.4f / med %.4f / max %.4f" % (summary["delta_min"] or -1, summary["delta_median"] or -1, summary["delta_max"] or -1))
log("SAVED entB_lt_full.json  %.0fs" % (time.time()-t0))
