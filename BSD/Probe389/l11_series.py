# -*- coding: utf-8 -*-
"""
L_p(T) series 复刻 (Sage pAdicLseriesOrdinary.series, padic_lseries.py verbatim)
校准靶: 11a1/p=3 series(3) = 2+3+3^2+2·3^3+O(3^5) + (1+3+O(3^2))T + (1+2·3+O(3^2))T^2 + O(3)T^3 + O(3)T^4 + O(T^5)

公式 (verbatim):
  measure(a, n) = z·(f(a/(p·w)) − f(a/w)/α),  z = 1/α^n,  w = p^{n-1}   [good reduction]
  series(n): L = Σ_{j=0}^{p^{n-1}-1} ( Σ_{a=1}^{p-1} teich[a]^eta · measure(teich[a]·γ^j) ) · (1+T)^j
  系数精度: aj[0].add_bigoh(padic_prec-2), aj[j].add_bigoh(bounds[j]);
  bounds = _e_bounds(n-1, prec) − c_bound;  L /= real_components (si=+1)
λ⁺ 泛函: 11a1 φ⁺ (free3 基) = [−1/2, −1, 1/5]  (锚 22 值全命中, 已验)
"""
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from fractions import Fraction as F
from l11_lambda import build_space, gaussian, kernel_basis, class_coords, expand_path

# ---------- p 进工具 (模 p^k 整数环) ----------

def egcd(a, b):
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = egcd(b, a % b)
    return (g, y1, x1 - (a // b) * y1)

def modinv(a, m):
    """模 m 逆元 (m 可为合数, 扩展欧几里得)."""
    g, x, _ = egcd(a % m, m)
    assert g == 1, "gcd(%d,%d)=%d ≠ 1" % (a % m, m, g)
    return x % m

def f2padic(x, pk):
    """Fraction → 模 pk 整数 (分母与 p 互素)."""
    if x is None:
        raise ValueError("∞ 不可 p 进化")
    return (x.numerator % pk) * modinv(x.denominator % pk, pk) % pk

def hensel_root(f, fp, r0, p, k):
    """Hensel 提升 f(x)=0 mod p^k, 初值 r0 (f(r0)≡0 mod p, fp(r0)≢0)."""
    x = r0 % p
    pk = p
    while pk < p ** k:
        pk *= p
        fv = f(x) % pk
        # x_{new} = x − fv/fp mod pk (Newton, 提升一阶)
        x = (x - fv * modinv(fp(x) % p, p)) % pk
    return x % (p ** k)

def alpha_ordinary(ap, p, prec):
    """x² − ap·x + p = 0 的单位根 α (ord_p(α)=0), Hensel 模 p^prec."""
    def f(x):
        return (x * x - ap * x + p)
    def fp(x):
        return (2 * x - ap)
    # 初值: 模 p 的根. 单位根 ⟹ α ≢ 0 mod p: 试 1..p−1
    r0 = None
    for r in range(1, p):
        if (r * r - ap * r) % p == 0:
            r0 = r
            break
    assert r0 is not None, "无模 p 单位根 (非 ordinary?)"
    return hensel_root(f, fp, r0, p, prec)

def teichmuller(a, p, k):
    """a (1..p−1) 的 Teichmuller 提升 ω(a) mod p^k: x_{m+1} = x_m^p 收敛."""
    x = a % p
    pk = p ** k
    for _ in range(40):
        xn = pow(x, p, pk)
        if xn == x:
            break
        x = xn
    return x % pk

# ---------- 模符号 λ⁺ 求值 (11a1) ----------

class Lambda11:
    def __init__(self, Nv, phi):
        self.Nv = Nv
        reps, idx, rel_rows = build_space(Nv, include_boundary=False)
        self.reps = reps
        self.ech3 = gaussian(rel_rows)
        _, self.free3 = kernel_basis(self.ech3, len(reps))
        self.phi = phi
    def __call__(self, r):
        w = expand_path(None, r, self.reps, self.Nv)
        w3 = class_coords(w, self.ech3, self.free3)
        return sum(self.phi[k] * w3[k] for k in range(len(self.free3)))

# ---------- series 复刻 ----------

def e_bounds(n, prec, p):
    """v_p(binomial(p^n, j)) 前缀: [∞, n, n−1,...] 逐点下降到 0."""
    bound = n
    next_drop = p
    res = [None]  # +Infinity
    for j in range(1, prec):
        if bound and j == next_drop:
            bound -= 1
            next_drop *= p
        res.append(bound)
    return res

def series_lp(p, ap, lam, real_components, n=3, prec=5, eta=0, c_bound=0):
    """复刻 pAdicLseriesOrdinary.series(n, prec, eta).  返回 (系数列表[Fraction], 精度界)."""
    si = 1 - 2 * (eta % 2)
    p_power = p ** (n - 1)
    gamma = 1 + p
    bounds = [None] + [b - c_bound for b in e_bounds(n - 1, prec, p)[1:]]
    padic_prec = max(bounds[1:]) + 5
    pk = p ** padic_prec
    res_series_prec = min(p_power, prec)
    # α 与 1/α
    alpha = alpha_ordinary(ap, p, padic_prec)
    alpha_inv = modinv(alpha, pk)
    # 系数 (模 pk 整数), 逐步 (1+T)^j
    coeffs = [0] * res_series_prec
    one_plus_T = [1]  # (1+T)^j 系数
    gamma_power = 1
    for j in range(p_power):
        s = 0
        for a in range(1, p):
            # Sage 语义: b = teich[a]·γ^j 为"未取模"精确整数 (mod pk 只在求值结果取)
            b = teichmuller(a, p, padic_prec) * gamma_power
            w = p ** (n - 1)
            # measure(b, n): z = α^{-n};  μ = z·(λ⁺(b/(p·w)) − λ⁺(b/w)/α)
            # Sage __call__ 语义: r = numer % denom / denom (归约到 [0,1))
            zn = pow(alpha_inv, n, pk)
            l1 = f2padic(lam(F(b % (p * w), p * w)), pk)
            l2 = f2padic(lam(F(b % w, w)), pk)
            mu = zn * (l1 - l2 * alpha_inv) % pk
            s = (s + mu) % pk
        for l in range(min(len(one_plus_T), res_series_prec)):
            coeffs[l] = (coeffs[l] + s * one_plus_T[l]) % pk
        one_plus_T = one_plus_T + [0]
        for l in range(len(one_plus_T) - 1, 0, -1):
            one_plus_T[l] = (one_plus_T[l] + one_plus_T[l - 1]) % pk
        gamma_power = gamma_power * gamma
    # 截断到证明精度
    out = []
    for l in range(res_series_prec):
        if l == 0:
            bd = padic_prec - 2
        else:
            bd = bounds[l]
        c = coeffs[l] % (p ** bd)
        out.append((c, bd))
    # L /= real_components (si=+1)
    if si == +1:
        rinv = modinv(real_components, pk)
        out = [((c * rinv) % (p ** bd), bd) for (c, bd) in out]
    return out

def fmt_series(out, p):
    parts = []
    for l, (c, bd) in enumerate(out):
        digits = []
        cc = c
        for _ in range(bd):
            digits.append(cc % p)
            cc //= p
        s = " + ".join(("%d·%d^%d" % (digits[k], p, k)) if k else str(digits[0])
                       for k in range(len(digits)) if digits[k])
        if not s:
            s = "0"
        parts.append("%sT^%d" % (s, l) if l else s)
    return " + ".join(parts)

if __name__ == "__main__":
    # 11a1: N=11, a₃ = −1, real_components = 1 (Δ = −11^5 < 0)
    lam = Lambda11(11, [F(-1, 2), F(-1, 1), F(1, 5)])
    print("11a1 λ⁺ 锚抽查: λ⁺(0) =", lam(0), " λ⁺(1/2) =", lam(F(1, 2)), " λ⁺(1/3) =", lam(F(1, 3)))
    out = series_lp(p=3, ap=-1, lam=lam, real_components=1, n=3, prec=5, eta=0, c_bound=0)
    print("11a1/p=3 series(3):", fmt_series(out, 3))
    print("Sage 期望          : 2+3+3^2+2·3^3+O(3^5) + (1+3+O(3^2))T + (1+2·3+O(3^2))T^2 + O(3)T^3 + O(3)T^4")
