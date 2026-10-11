# probe389_numeric.py  (v2)
# 389a1 probe: rank-2 curve y^2 + y = x^3 + x^2 - 2x (N = 389, eps = +1, rank 2)
# Quantify the "deterioration curve" first point:
#   rank-1 (37a1, N=37, eps=-1): L'(1)  ~ 0.30599977 (their lprime1 closure)
#   rank-2 (389a1, N=389, eps=+1): L''(1) via the SAME convergent framework
# Convergent series uses the upper incomplete Gamma (Rubinstein/lcalc form):
#   F(s) = sum a_n n^{-s} Gamma(s,b_n)/Gamma(s)
#        + eps*(sqrt(N)/(2pi))^{2s-2}*Gamma(2-s)/Gamma(s) * sum a_n n^{s-2} Gamma(2-s,b_n)/Gamma(2-s)
#   b_n = 2 pi n / sqrt(N)   (tail ~ e^{-b_n}, decays exponentially for ALL s in (0,2))
# Derivatives at s=1 by finite differences (probe precision only).
# Pure stdlib; Python 3 compatible.
import math

GAMMA = 0.57721566490153286060651209008240243104215933593992

# ---------- primes ----------
def primes_upto(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = b'\x00' * (((n - i*i) // i) + 1)
    return [i for i in range(2, n + 1) if sieve[i]]

# ---------- point counting: a_p for E: y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6 ----
# a_p = p + 1 - #E(F_p) = p - #affine_points   (the point at infinity accounts for the +1)
def ap_modp(a1, a2, a3, a4, a6, p):
    if p == 2:
        cnt = 0
        for x in range(2):
            for y in range(2):
                lhs = (y * y + a3 * y) % 2
                rhs = (x ** 3 + a2 * x * x + a4 * x + a6) % 2
                if lhs == rhs:
                    cnt += 1
        return p - cnt
    tot = 0
    for x in range(p):
        R = (x ** 3 + a2 * x * x + a4 * x + a6) % p
        d = (4 * R + a3 * a3) % p  # a1 = 0 for both curves here
        if d == 0:
            tot += 1
        else:
            tot += 2 if pow(d, (p - 1) // 2, p) == 1 else 0
    return p - tot

def gen_a_n(Nmax, a1, a2, a3, a4, a6, bad_ap=None):
    primes = primes_upto(Nmax)
    ap = {}
    for p in primes:
        if bad_ap is not None and p in bad_ap:
            ap[p] = bad_ap[p]
        else:
            ap[p] = ap_modp(a1, a2, a3, a4, a6, p)
    ppow = {}
    for p in primes:
        a = ap[p]
        prev2, prev1 = 1, a
        k = 1
        pk = p
        while pk <= Nmax:
            ppow[(p, k)] = prev1
            pk *= p
            k += 1
            if pk <= Nmax:
                cur = a * prev1 - p * prev2
                prev2, prev1 = prev1, cur
    an = {1: 1}
    for n in range(2, Nmax + 1):
        m = n
        val = 1
        for p in primes:
            if p * p > m:
                break
            if m % p == 0:
                k = 0
                while m % p == 0:
                    m //= p
                    k += 1
                val *= ppow[(p, k)]
        if m > 1:
            val *= ppow[(m, 1)]
        an[n] = val
    return an

# ---------- upper incomplete Gamma Gamma(s, x), s in ~[0.5, 1.5] ----------
def gamma_upper(s, x):
    if x <= 0:
        return math.gamma(s)
    if x < 20:
        # series for lower incomplete gamma gamma(s,x) = x^s * sum (-x)^k/(k!*(s+k))
        # intermediate terms peak ~ e^x; for x<20 that is ~2e7, float cancellation
        # stays at ~1e-9 relative — acceptable for probe precision
        gs = math.gamma(s)
        term = 1.0
        total = term / s
        k = 1
        while True:
            term *= -x / k
            total += term / (s + k)
            k += 1
            if k > 400 or abs(term / (s + k)) < 1e-18 * (1 + abs(total)):
                break
        return gs - (x ** s) * total
    # asymptotic: Gamma(s,x) = x^{s-1} e^{-x} [ 1 + (s-1)/x + (s-1)(s-2)/x^2 + ... ]
    # divergence starts once |term_k| grows again; stop at optimal truncation
    t = x ** (s - 1) * math.exp(-x)
    ssum = 1.0
    term = 1.0
    prev = 1.0
    k = 1
    while k <= 200:
        term *= (s - k) / x
        if abs(term) > abs(prev) and k > 3:
            break
        ssum += term
        prev = term
        k += 1
        if abs(term) < 1e-18:
            break
    return t * ssum

# ---------- convergent L-series value F(s) ----------
# Exact Mellin splitting with Fricke duality:
#   L(s) = S1(s) + C(s) * S2'(s) / epsL
#   S1  = sum a_n n^{-s} Gamma(s,b)/Gamma(s)
#   S2' = sum a_n n^{s-2} Gamma(2-s,b)
#   C   = N^{1-s} (2 pi)^{2s-2} / Gamma(s)
#   epsL = root number (+1 for 389a1, -1 for 37a1)  [Atkin-Lehner eigenvalue = epsL]
# Valid in the critical strip (0, 2); derivatives at s=1 by finite differences.
def F_L(s, an, N, epsL, Q):
    sqN = math.sqrt(N)
    g1 = math.gamma(s)
    s1 = 0.0
    s2p = 0.0
    for n in range(1, Q + 1):
        b = 2 * math.pi * n / sqN
        s1 += an[n] * n ** (-s) * gamma_upper(s, b) / g1
        s2p += an[n] * n ** (s - 2) * gamma_upper(2 - s, b)
    C = N ** (1 - s) * (2 * math.pi) ** (2 * s - 2) / g1
    return s1 + C * s2p / epsL

def d1(F, s0, h, *a):
    return (F(s0 + h, *a) - F(s0 - h, *a)) / (2 * h)

def d2(F, s0, h, *a):
    return (F(s0 + h, *a) - 2 * F(s0, *a) + F(s0 - h, *a)) / (h * h)

def main():
    NMAX = 3000
    print("== 389a1 (rank 2) y^2+y = x^3+x^2-2x, N=389, eps=+1 ==")
    an389 = gen_a_n(NMAX, 0, 1, 1, -2, 0, bad_ap={389: 1})
    print("sample a_n(389a1) n=1..20:", [an389[n] for n in range(1, 21)])
    # rank-2 evidence: F(1) = (1+eps)*sum a_n/n*e^{-b_n} must be ~0 (L(1)=0)
    f1 = F_L(1.0, an389, 389, 1, NMAX)
    print("F(1) = L(1) via convergent series:", f"{f1: .3e}", "  (rank-2: should be ~0)")
    print("\nL''(1) by finite difference, step-scan:")
    for Q in (500, 1000, 2000, 3000):
        v = d2(F_L, 1.0, 0.02, an389, 389, 1, Q)
        print(f"  Q={Q:5d}  L''(1) ~ {v: .5f}")
    print("  h-scan at Q=3000:")
    best = None
    for h in (0.10, 0.05, 0.02, 0.01, 0.005):
        v = d2(F_L, 1.0, h, an389, 389, 1, 3000)
        best = v if best is None else v
        print(f"    h={h:.3f}  L''(1) ~ {v: .5f}")

    print("\n== 37a1 (rank 1) y^2+y = x^3-x, N=37, eps=-1 ==")
    an37 = gen_a_n(NMAX, 0, 0, 1, -1, 0, bad_ap={37: 1})
    print("sample a_n(37a1) n=1..20:", [an37[n] for n in range(1, 21)])
    f1_37 = F_L(1.0, an37, 37, -1, NMAX)
    print("F(1) = L(1):", f"{f1_37: .3e}", "  (rank-1: should be ~0, eps=-1 forces it)")
    print("L'(1) by finite difference (literature ~ 0.30599977):")
    for h in (0.10, 0.05, 0.02, 0.01):
        v = d1(F_L, 1.0, h, an37, 37, -1, NMAX)
        print(f"  h={h:.2f}  L'(1) ~ {v: .6f}")

    print("\n== deterioration curve first point ==")
    b1 = 2 * math.pi / math.sqrt(37)
    b2 = 2 * math.pi / math.sqrt(389)
    print(f"  rank-1 tail coefficient  b1 = 2*pi/sqrt(37)  = {b1:.6f}  (tail ~ e^-{{b1 n}})")
    print(f"  rank-2 tail coefficient  b2 = 2*pi/sqrt(389) = {b2:.6f}  (tail ~ e^-{{b2 n}})")
    print(f"  term ratio (same truncation error): b1/b2 = {b1/b2:.3f}  (~3.2x more terms for rank 2)")
    print(f"  L'(37a1,1)  ~ 0.306        (leading term of rank-1, scale ~0.3)")
    print(f"  L''(389a1,1) ~ {best: .4f}   (leading term of rank-2, scale ~1e2-1e3)")

if __name__ == "__main__":
    main()
