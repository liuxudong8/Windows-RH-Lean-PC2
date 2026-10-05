# -*- coding: utf-8 -*-
"""
骨架A (i) degree-2 数值延拓：L(E,s) 中心值判秩
方法：Dokchitser 型对称化——对 Γ(s) 因子、函数方程 Λ(s)=w·Λ(2−s)：
  Λ(s) = Σ_n c_n [ w·Γ(2−s, b_n) + Γ(s, b_n) ],  b_n = 2πn/√N
  L(s) = (2π/√N)^s / Γ(s) · Λ(s)
第一阶段：ℚ 端 37a1（N=37, w=−1），对照 LMFDB L′(E,1)≈0.30599977 闭环
第二阶段：ℚ(√5) 端 base change（N_K=37², w_K=−1 推导），判秩
"""
import math
from mpmath import mp, mpf, gammainc, gamma, pi, exp, log, diff, mpmathify

mp.dps = 50

# ---------- ℚ 端 37a1 系数 a_n ----------
def legendre_sq_count(p, f):
    """y² = f(x) 在 𝔽_p 上的点数"""
    n = 0
    for x in range(p):
        r = f(x) % p
        if r == 0:
            n += 1
        elif pow(r, (p - 1) // 2, p) == 1:
            n += 2
    return n

def count_Fp_y2y(p):
    # y²+y = x³−x ⟺ (2y+1)² = 4x³−4x+1
    return legendre_sq_count(p, lambda x: 4 * x * x * x - 4 * x + 1)

def ap_Q(p):
    if p == 37:
        return -1  # 37a1 分裂乘性约化 a_37 = −1
    return p - count_Fp_y2y(p)  # count = #E(𝔽_p) − 1

def build_bn(nmax, ap_fn, bad, local_pow):
    """乘性 Dirichlet 系数：b_1=1；b_{p^k} 由局部因子确定；b_{mn}=b_m b_n ((m,n)=1)
    local_pow: 'ell' 椭圆局部因子 (1−a X + p X²)^{-1}；'mult' 乘性 (1−a X)^{-1}"""
    b = [0] * (nmax + 1)
    b[1] = 1
    # 素数幂系数表
    pk = {}
    def ell_coeff(a, p, K):
        # (1−aX+pX²)^{-1} 展开 c_k：c_0=1,c_1=a,c_k=a c_{k−1}−p c_{k−2}
        c = [1] * (K + 1)
        if K >= 1:
            c[1] = a
        for k in range(2, K + 1):
            c[k] = a * c[k - 1] - p * c[k - 2]
        return c
    def mult_coeff(a, K):
        return [a ** k for k in range(K + 1)]
    for p in range(2, nmax + 1):
        isp = True
        d = 2
        while d * d <= p:
            if p % d == 0:
                isp = False
                break
            d += 1
        if not isp:
            continue
        K = 0
        pkv = p
        while pkv <= nmax:
            K += 1
            pkv *= p
        if p in bad:
            coeffs = mult_coeff(ap_fn(p), K)
        else:
            coeffs = ell_coeff(ap_fn(p), p, K)
        pk[(p, 1)] = coeffs[:2]
        for k in range(2, K + 1):
            pk[(p, k)] = coeffs[:k + 1]
    # 组合
    def fill(n, idx_p, fac_pow):
        # 用最小素数因子分解
        pass
    # 直接对每个 n 做素因子分解
    for n in range(2, nmax + 1):
        m = n
        val = 1
        p = 2
        while p * p <= m:
            if m % p == 0:
                e = 0
                while m % p == 0:
                    m //= p
                    e += 1
                val *= pk[(p, e)][e]
            p += 1
        if m > 1:
            e = 1
            val *= pk[(m, e)][e]
        b[n] = val
    return b

# ---------- 通用 L 求值 ----------
def Lambda(s, coeffs, N, w, nmax):
    sqN = mpf(N) ** mpf('0.5')
    s = mpmathify(s)
    tot = mpf('0')
    for n in range(1, nmax + 1):
        c = coeffs[n]
        if c == 0:
            continue
        bn = 2 * pi * n / sqN
        # ∫_1^∞ v^{a} e^{−bv}dv = b^{−a−1}·Γ(a+1, b)
        # Λ(s) = Σ a_n[ ε·b^{s−2}·Γ(2−s,b) + b^{−s}·Γ(s,b) ]
        g1 = gammainc(2 - s, bn, mp.inf)
        g2 = gammainc(s, bn, mp.inf)
        tot += c * (w * bn ** (s - 2) * g1 + bn ** (-s) * g2)
    return tot

def L(s, coeffs, N, w, nmax):
    sqN = mpf(N) ** mpf('0.5')
    lam = Lambda(s, coeffs, N, w, nmax)
    return (2 * pi / sqN) ** s / gamma(s) * lam

def Lprime(num, coeffs, N, w, nmax, h=mpf('1e-3')):
    h = mpf(h)
    return (L(num + h, coeffs, N, w, nmax) - L(num - h, coeffs, N, w, nmax)) / (2 * h)

# ================= 第一阶段：ℚ 端 37a1 =================
print('===== 第一阶段：ℚ 端 37a1（N=37，w=−1）=====')
NQ = 37
nmaxQ = 400
badQ = {37}
coeffsQ = build_bn(nmaxQ, ap_Q, badQ, 'ell')
# a_p 抽样核对
for p in [2, 3, 5, 7, 11, 13]:
    print('  a_%d = %d' % (p, ap_Q(p)))
l1 = L(mpf('1'), coeffsQ, NQ, -1, nmaxQ)
print('  L(1) =', l1)
lp = Lprime(mpf('1'), coeffsQ, NQ, -1, nmaxQ)
print("  L'(1) =", lp, '  （LMFDB 37.a1 期望 ≈ 0.3059997738346523）')

# ================= 第二阶段：ℚ(√5) 端 base change =================
print('===== 第二阶段：ℚ(√5) 端 37a1 base change（N_K=1369，w_K=−1 推导）=====')
# b_n 构造：分裂素 b_{p^k} 由 (1−a_p X + pX²)^{-2}；惰性素 (1−a_𝔭 X + p²X²)^{-1}；分歧 5 (1−a_5 X + 5X²)^{-1}
# 37 惰性乘性（非分裂）局部因子 (1 − (+1) X)^{-1}
nmaxK = 400
bK = [0] * (nmaxK + 1)
bK[1] = 1

def is_split(p):
    return p % 5 in (1, 4)

def local_split_coeffs(a, p, K):
    # (1−aX+pX²)^{-2}：先求 α_k（单因子 c_k）再卷积平方
    c = [1] * (K + 1)
    if K >= 1:
        c[1] = a
    for k in range(2, K + 1):
        c[k] = a * c[k - 1] - p * c[k - 2]
    d = [0] * (K + 1)
    for i in range(K + 1):
        s = 0
        for j in range(i + 1):
            s += c[j] * c[i - j]
        d[i] = s
    return d

def local_inert_coeffs(a, p, K):
    # (1−aX+p²X²)^{-1}
    c = [1] * (K + 1)
    if K >= 1:
        c[1] = a
    for k in range(2, K + 1):
        c[k] = a * c[k - 1] - p * p * c[k - 2]
    return c

# 预计算各类型素数的局部系数表（在各自 Nm 变量上）
#   分裂素 p：局部因子 (1−aX+pX²)^{-2}，变量 Nm=p        ⟹ b_{p^k} = d_k
#   惰性素 p：局部因子 (1−aX+p²X²)^{-1}，变量 Nm=p²     ⟹ b_{p^{2k}} = c_k，b_{p^{2k+1}} = 0
#   分歧素 5：(1−aX+5X²)^{-1}，变量 Nm=5                ⟹ b_{5^k} = c_k
#   37 惰性乘性（非分裂）：(1−X)^{-1}，变量 Nm=37²       ⟹ b_{37^{2k}} = 1
split_tab, inert_tab, ram_tab = {}, {}, {}
for p in range(2, nmaxK + 1):
    isp = True
    d = 2
    while d * d <= p:
        if p % d == 0:
            isp = False
            break
        d += 1
    if not isp:
        continue
    if is_split(p):
        # 分裂素：p^k ≤ nmax
        K = 0
        pkv = p
        while pkv <= nmaxK:
            K += 1
            pkv *= p
        split_tab[p] = local_split_coeffs(ap_Q(p), p, K)
    elif p == 5:
        # 分歧：5^k ≤ nmax
        K = 0
        pkv = 5
        while pkv <= nmaxK:
            K += 1
            pkv *= 5
        ram_tab = local_inert_coeffs(ap_Q(5), 5, K)
    else:
        # 惰性：p^{2k} ≤ nmax（Nm=p²）
        K = 0
        pkv = p * p
        while pkv <= nmaxK:
            K += 1
            pkv *= p * p
        if p == 37:
            inert_tab[37] = [1] * (K + 1)   # 非分裂乘性 a=+1：(1−X)^{-1} 系数全 1
        else:
            a = ap_Q(p) ** 2 - 2 * p
            inert_tab[p] = local_inert_coeffs(a, p, K)

for n in range(2, nmaxK + 1):
    m = n
    val = 1
    p = 2
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if p == 5:
                val *= ram_tab[e]
            elif is_split(p):
                val *= split_tab[p][e]
            else:
                if e % 2 == 1:
                    val = 0
                else:
                    val *= inert_tab[p][e // 2]
        p += 1
    if m > 1:
        p = m
        if p == 5:
            val *= ram_tab[1]
        elif is_split(p):
            val *= split_tab[p][1]
        else:
            val = 0   # 惰性素奇数幂（n=p 奇次）系数为 0
    bK[n] = val

# 抽样核对 b_n（分裂素 b_p = 2a_p；惰性素 b_{p²} = a_p²−2p）
print('  抽样：b_2(惰性 4)=%d（期望 a₂²−4 = (−2)²−4=0）' % bK[4])
print('  抽样：b_3(惰性 9)=%d（期望 a₃²−6 = 9−6=3）' % bK[9])
print('  抽样：b_11(分裂)=%d（期望 2·a₁₁ = 2·(−5)=−10）' % bK[11])
print('  抽样：b_5(分歧)=%d（期望 a₅ = −2）' % bK[5])
print('  抽样：b_7²(惰性 49)=%d（期望 a₇²−14 = 1−14=−13）' % bK[49])

NK = 37 * 37
l1k = L(mpf('1'), bK, NK, -1, nmaxK)
print('  L_K(1) =', l1k)
lpk = Lprime(mpf('1'), bK, NK, -1, nmaxK)
print("  L_K'(1) =", lpk)
