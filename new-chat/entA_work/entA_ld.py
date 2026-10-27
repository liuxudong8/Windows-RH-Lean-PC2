# -*- coding: utf-8 -*-
"""入口 A 第二实验（解析精简版）：对数导数实部峰口径（离线零点计数器）

理论：−(ζ_K′/ζ_K)(s) = Σ_ρ 1/(s−ρ) − 极点项 − …。对 s=1/2+it：
  在线零点：Re 1/(i(t−γ)) = 0 ⟹ 无实部贡献
  离线零点（σ=1/2−δ）：Re 1/(δ+i(t−γ)) = δ/(δ²+(t−γ)²) ⟹ 每零点正峰，∫dt = π（与 δ 无关）
素数项背景：F0(t)=Re Σ_{p≤X}(1+χ₅(p))log p·p^{−1/2−it}
  rms ≈ sqrt(Σa²)（t 平均，相干 ~1/log p）
  区间积分背景：∫_{T/2}^T F0(t)dt = Σ_p (1+χ)√p^{-1}·[sin(T log p)−sin((T/2)log p)]（边界振荡项）

本实验输出（全部解析/近解析）：
  (A) 背景 rms 与单峰高对照（分辨率）：1/δ vs sqrt(Σa²)
  (B) 全局积分信噪比：K·π vs 背景积分边界项（K=430 / 21.9 万两口径）
  (C) 局部峰分辨数值测试（小网格，确认峰形状/面积）
"""
import numpy as np, json, time, math

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_ld.json"
t0 = time.time()
T = 6e5; lam = math.log(T)
X = 1_000_000

def sieve(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
ps = sieve(X)
chi5 = np.where(ps % 5 == 0, 0, np.where((ps % 5 == 1) | (ps % 5 == 4), 1, -1))
a1 = (1.0 + chi5) * np.log(ps) / np.sqrt(ps)      # 对数导数素项系数
lp = np.log(ps)
sum_a2 = float(np.sum(a1 * a1))
rms_bg = math.sqrt(sum_a2)
# 区间积分背景（边界项，解析）
int_bg = float(np.sum(a1 * (np.sin(T * lp) - np.sin((T / 2) * lp)) / lp))
print("X=%.0f Np=%d  Σa²=%.3f  rms|F0|=%.3f" % (X, len(ps), sum_a2, rms_bg), flush=True)
print("背景区间积分(解析)=%+.3f  |边界项|=%.3f" % (int_bg, abs(int_bg)), flush=True)

# 峰面积：K 个零点全在区间内 ⟹ K·π（解析）；边界截断校正小（γ 距边界 <~5δ 时）
D_LIST = [0.02, 0.05, 0.1, 0.2, 0.4]
K_LIST = [430, 5000, 50000, 219000, 430000]
rng = np.random.default_rng(20261023)
Z = np.sort(np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")["zeta"])

rows = []
for delta in D_LIST:
    for K in K_LIST:
        gammas = rng.choice(Z, size=K, replace=False)
        area = float(np.sum(np.arctan((T - gammas) / delta) - np.arctan((T/2 - gammas) / delta)))
        peak_h = 1.0 / delta                       # 单峰峰值（t=γ 处）
        snr_h = peak_h / rms_bg                    # 单峰高 vs 背景 rms
        snr_int = area / abs(int_bg) if int_bg != 0 else math.inf
        rows.append(dict(delta=delta, K=K, area_pk=area, area_over_pi=area/math.pi,
                         peak_h=peak_h, rms_bg=rms_bg, snr_h=snr_h,
                         bg_int=int_bg, snr_int=snr_int))
        print("δ=%.3f K=%7d  峰面积=%.2f(%.2f·π)  单峰高=%.0f vs 背景rms=%.2f (SNR_h=%.3f)  积分SNR=%.4f"
              % (delta, K, area, area/math.pi, peak_h, rms_bg, snr_h, snr_int), flush=True)

# 局部峰分辨数值测试（5 个 γ × 4 个 δ，细网格确认峰形状与面积）
peaks_detail = []
g5 = rng.choice(Z, size=5, replace=False)
def F0_local(tgrid):
    out = np.zeros(len(tgrid))
    for i in range(0, len(tgrid), 500):
        tb = tgrid[i:i+500]
        ph = np.exp(-1j * np.outer(lp, tb))
        out[i:i+500] = np.real(a1 @ ph)
    return out
for delta in [0.02, 0.05, 0.1, 0.2]:
    for g in g5:
        dt_f = min(delta / 8.0, 0.02)
        tg = np.arange(g - 6*delta, g + 6*delta, dt_f)
        F = F0_local(tg)
        pk = delta / (delta*delta + (tg - g)**2)
        Fp = F + pk
        # 数值面积（峰-背景，仅正部分近似）
        num_area = float(np.sum(pk) * dt_f)
        peak_h = float(np.max(pk))
        bg_rms_loc = float(np.sqrt(np.mean(F**2)))
        peaks_detail.append(dict(delta=delta, g=float(g), dt=dt_f, num_area=num_area,
                                 peak_h=peak_h, bg_rms_loc=bg_rms_loc,
                                 resolv=peak_h > 2*bg_rms_loc))
        print("  细峰 δ=%.3f γ=%.0f dt=%.4f 面积=%.3f(理论π=3.1416) 峰高=%.1f 背景rms=%.2f %s"
              % (delta, g, dt_f, num_area, peak_h, bg_rms_loc, "✓" if peak_h > 2*bg_rms_loc else "✗"), flush=True)

json.dump(dict(meta=dict(T=T, X=X, Np=len(ps), sum_a2=sum_a2, rms_bg=rms_bg, int_bg=int_bg),
               rows=rows, peaks_detail=peaks_detail, runtime_s=time.time()-t0),
          open(OUT, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("\nsaved", OUT, "%.1fs" % (time.time()-t0))
