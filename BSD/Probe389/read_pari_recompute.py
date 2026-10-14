# -*- coding: utf-8 -*-
"""
PARI 真模符号重算 series(3): 校准闭环验证.
输入: ms11a1_series_out.txt / ms11a1_extra_out.txt (PARI mseval {0,r} 值, 非尖点端点).
换算: f_true({oo,r}) = f_H1({0,r}) + 1/5   (f_H1({0,oo}) = -1/5, 由锚 M(0)=1/5 反推).
尖点端点 (c ≡ 0 mod 11): 用 M+ 对称性 f(1-r) = f(r) 补 (PARI 对尖点端点的 mseval 是
调和积分的特殊值, 非 H1 值; 实测 {0,11/27}=4/5 破坏对称, 真值 = {0,16/27} = -3/2).
目标: Σ_j s_j ≡ 68 mod 243 (Sage series(3) T^0 = 2+3+3^2+2*3^3+O(3^5)).
"""
import re
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from fractions import Fraction as F
from l11_series import modinv, f2padic, teichmuller, alpha_ordinary, e_bounds

PADIR = r"C:\proj2\BSD\Probe389"

def parse_pari(fname):
    d = {}
    with open(fname, encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"r=(\d+)/(\d+)\s*:\s*([^\s]+)", line.strip())
            if m:
                num, den, val = int(m.group(1)), int(m.group(2)), m.group(3)
                d[F(num, den)] = F(val)
    return d

pari = parse_pari(PADIR + r"\ms11a1_series_out.txt")
pari.update(parse_pari(PADIR + r"\ms11a1_extra_out.txt"))

def f_h1(r):
    """f_H1({0,r}) — 非尖点端点用 PARI 实测; 尖点端点 (分子 c ≡ 0 mod 11, 即 11/27, 22/27)
    的 mseval 是调和积分特殊值 (实测 {0,11/27}=4/5 破坏对称), 强制用对称 f(1-r) = f(r)."""
    num, den = r.numerator, r.denominator
    if num % 11 == 0:
        alt = F(1) - r
        if alt in pari:
            return pari[alt]
        raise KeyError("cusp endpoint, no symmetric partner for %s" % r)
    if r in pari:
        return pari[r]
    alt = F(1) - r
    if alt in pari:
        return pari[alt]
    raise KeyError("no PARI value for %s / %s" % (r, alt))

def f_true(r):
    """eclib {oo,r} = f_H1({0,r}) + 1/5."""
    return f_h1(r) + F(1, 5)

# ---- 复刻 series 管道 (与 debug_trace_series.py 一致) ----
p, ap, n, prec = 3, -1, 3, 5
p_power = p ** (n - 1)
bounds = [None] + [b for b in e_bounds(n - 1, prec, p)[1:]]
padic_prec = max(bounds[1:]) + 5
pk = p ** padic_prec
alpha = alpha_ordinary(ap, p, padic_prec)
alpha_inv = modinv(alpha, pk)
zn = pow(alpha_inv, n, pk)
teich = [teichmuller(a, p, padic_prec) for a in range(p)]
w = p ** (n - 1)
gamma = 1 + p

print("p=%d n=%d padic_prec=%d pk=%d alpha=%d alpha_inv=%d zn=%d" % (p, n, padic_prec, pk, alpha, alpha_inv, zn))

total = 0
s_list = []
rows = []
for j in range(p_power):
    gamma_power = pow(gamma, j)
    s = 0
    for a in range(1, p):
        b = teich[a] * gamma_power
        rb27 = F(b % (p * w), p * w)
        rb9 = F(b % w, w)
        l1 = f_true(rb27)
        l2 = f_true(rb9)
        mu = zn * (f2padic(l1, pk) - f2padic(l2, pk) * alpha_inv) % pk
        s = (s + mu) % pk
        rows.append((j, a, b, rb27, l1, rb9, l2, mu))
    s_list.append(s)
    total = (total + s) % pk

tgt = (1 - alpha_inv) ** 2 % pk * f2padic(F(1, 5), pk) % pk
print("--- 逐项 (PARI 真值) ---")
for (j, a, b, rb27, l1, rb9, l2, mu) in rows:
    print("j=%d a=%d b=%d  f(%s)=%s  f(%s)=%s  mu=%d" % (j, a, b, str(rb27), str(l1), str(rb9), str(l2), mu))
print("s_j =", s_list)
print("Σ s_j = %d mod 3^7 → mod 3^5 = %d   (Sage 期望 68)" % (total, total % (p ** 5)))
print("目标恒等式 (1-1/alpha)^2·λ(0) = %d → %d" % (tgt, tgt % (p ** 5)))
print("命中 68: %s" % (total % (p ** 5) == 68))
