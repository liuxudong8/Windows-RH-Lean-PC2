# -*- coding: utf-8 -*-
"""入口 A 第三实验：σ>1/2 正则化对数导数实部（峰宽测量机制验证）

F(t;ε) = Re[−(ζ_K′/ζ_K)(1/2+ε+it)]
  = Σ_ρ (ε+δ_ρ)/((ε+δ_ρ)²+(t−γ)²) + 素项(σ>1/2 收敛，小)
在线零点 δ=0：峰宽 ε、高 1/ε
离线零点 δ>0：峰宽 ε+δ（更宽）
素项背景：Σ a_p p^{−ε} e^{−it lp}，功率 Σa²p^{−2ε}（σ=1/2+ε 收敛）

验证：(1) 在线峰宽均匀 ε（数据全在线假设的签名）
      (2) 背景在 ε>0 收敛（与 ε=0 的发散对照）
      (3) 峰宽分辨率：δ 变化是否可测（dt<ε 时）
"""
import numpy as np, json, time, math
OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entA_work\entA_eps.json"
t0 = time.time()
T = 6e5
X = 300_000                      # 素数表（小，背景收敛快，σ>1/2）
def sieve(n):
    s = np.ones(n+1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
ps = sieve(X)
chi5 = np.where(ps % 5 == 0, 0, np.where((ps % 5 == 1) | (ps % 5 == 4), 1, -1))
a1 = (1.0 + chi5) * np.log(ps) / np.sqrt(ps)
lp = np.log(ps)
Z = np.sort(np.load(r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz")["zeta"])
t0c = time.time()

def Feps(tgrid, eps, gamma_win):
    """F(t;ε)=素数背景 + 窗口内零点的 ε 峰"""
    n = len(tgrid)
    bg = np.zeros(n)
    for i in range(0, n, 3000):
        tb = tgrid[i:i+3000]
        ph = np.exp(-1j * np.outer(lp, tb))
        bg[i:i+3000] = np.real((a1 * np.exp(-eps * lp)) @ ph)
    peaks = np.zeros(n)
    g = gamma_win.reshape(-1, 1); tt = tgrid.reshape(1, -1)
    peaks = (eps / (eps*eps + (tt - g)**2)).sum(axis=0)
    return bg + peaks

EPS_LIST = [0.05, 0.1, 0.2]
res = {}
for eps in EPS_LIST:
    # 背景功率（解析）
    bg_pow = float(np.sum(a1*a1*np.exp(-2*eps*lp)))
    # 选一个 t 窗口（含 ~80 个零点，窗口宽 ~22）
    g0 = Z[len(Z)//2]
    win_half = 11.0
    gwin = Z[(Z > g0-win_half) & (Z < g0+win_half)]
    dt = min(eps/4.0, 0.01)
    tg = np.arange(g0-win_half, g0+win_half, dt)
    F = Feps(tg, eps, gwin)
    # 峰检测：局部极大（高于背景 rms 2 倍）
    bg_rms = math.sqrt(bg_pow)
    peaks_found = 0
    thr = bg_rms * 2.0
    for j in range(1, len(F)-1):
        if F[j] > F[j-1] and F[j] > F[j+1] and F[j] > thr:
            peaks_found += 1
    res[eps] = dict(eps=eps, bg_pow=bg_pow, bg_rms=bg_rms, n_win=len(gwin),
                    peaks_found=peaks_found, dt=dt,
                    supF=float(np.max(F)), rmsF=float(np.sqrt(np.mean(F**2))),
                    thr=thr)
    print("ε=%.2f  背景功率=%.4f(rms=%.2f)  窗口零点=%d  检测峰数=%d  窗口宽=%.0f  预期峰数=%d  dt=%.4f"
          % (eps, bg_pow, bg_rms, len(gwin), peaks_found, 2*win_half, len(gwin), dt), flush=True)
    # 峰高统计（真实峰应在 ~1/ε 附近）
    fmax = float(np.max(F))
    print("   sup|F|=%.2f（在线峰高理论 1/ε=%.1f）  rms=%.2f" % (fmax, 1.0/eps, float(np.sqrt(np.mean(F**2)))), flush=True)

json.dump(dict(meta=dict(T=T, X=X), res=res, runtime_s=time.time()-t0),
          open(OUT, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("saved", OUT, "%.1fs" % (time.time()-t0c))
