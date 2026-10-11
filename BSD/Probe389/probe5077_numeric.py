# probe5077_numeric.py  --  deterioration curve, point 2
# 5077a1 : y^2 + y = x^3 - 7x + 6  (N = 5077 prime, rank 3, eps = -1)
# BGZ classic rank-3 curve.  Targets (Cremona ecdata Table 4 / BSD):
#   L'''(1)/6 = 1.73184990,  Omega = 4.151687983,  R = 0.41714355,  Sha = 1
# Point-2 experiment: epsilon flips BACK to -1 while rank rises to 3.
# Parity sieve must PARTLY revive: (0,3)/(2,1) die, (1,2)/(3,0) survive.
# Numeric fingerprint of rank 3: F(1) = F'(1) = F''(1) ~ 0, F'''(1) ~ 10.391.
# Same convergent pipeline as probe389_numeric.py (point 1), pure stdlib.
import math

N = 5077
EPS = -1.0
BAD_AP = {5077: 1}          # p = N multiplicative split; 5077^2 > Q so no effect
A1, A2, A3, A4, A6 = 0, 0, 1, -7, 6

# ---------------- a_p point counting: a_p = p - #affine(F_p) ----------------
def ap_modp(p):
    if p == 2:
        cnt = 0
        for x in range(2):
            for y in range(2):
                lhs = (y * y + A3 * y) % 2
                rhs = (x ** 3 + A2 * x * x + A4 * x + A6) % 2
                if lhs == rhs:
                    cnt += 1
        return p - cnt
    tot = 0
    for x in range(p):
        R = (x ** 3 + A2 * x * x + A4 * x + A6) % p
        d = (4 * R + A3 * A3) % p
        if d == 0:
            tot += 1
        else:
            tot += 2 if pow(d, (p - 1) // 2, p) == 1 else 0
    return p - tot

def primes_upto(m):
    s = bytearray(b'\x01') * (m + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = b'\x00' * len(s[i * i::i])
    return [i for i in range(2, m + 1) if s[i]]

def gen_a_n(Nmax):
    primes = primes_upto(Nmax)
    ap = {}
    for p in primes:
        ap[p] = BAD_AP[p] if p in BAD_AP else ap_modp(p)
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

# ---------------- upper incomplete Gamma (series / optimal truncation) ------
def gamma_upper(s, x):
    if x <= 0:
        return math.gamma(s)
    if x < 20:
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
    total = x ** (s - 1) * math.exp(-x)
    term = total
    k = 1
    while True:
        term *= (s - k) / x
        if k > 2 and abs(term) > abs(total):
            total -= term
            break
        total += term
        if abs(term) < 1e-17 * abs(total) or k > 200:
            break
        k += 1
    return total

# ---------------- convergent L-series ----------------
SQN = math.sqrt(N)

# NOTE (fixed): S2' must NOT divide by Gamma(2-s).  The upper-incomplete Gamma(s,x)
# -> Gamma(s) as x -> oo, so the sum n^{s-2} * Gamma(2-s,b_n) already carries the
# Gamma(2-s) factor absorbed by C(s) = N^{1-s}(2pi)^{2s-2}/Gamma(s).  Dividing by
# Gamma(2-s) injects a spurious first-order term ~ psi(1)*C*S2'/eps at s=1
# (psi(1) = -0.5772), which broke 37a1/5077a1 slopes.  probe389_numeric.py (verified
# to 0.004% on 37a1 L'(1)) has no such division; match it exactly.
def F_L(s, an, Q):
    gs = math.gamma(s)
    S1 = 0.0
    S2p = 0.0
    for n in range(1, Q + 1):
        bn = 2.0 * math.pi * n / SQN
        S1 += an[n] * n ** (-s) * gamma_upper(s, bn) / gs
        S2p += an[n] * n ** (s - 2.0) * gamma_upper(2.0 - s, bn)
    C = N ** (1.0 - s) * (2.0 * math.pi) ** (2.0 * s - 2.0) / gs
    return S1 + C * S2p / EPS

def d1(F, x, h):  return (F(x + h) - F(x - h)) / (2.0 * h)
def d2(F, x, h):  return (F(x + h) - 2.0 * F(x) + F(x - h)) / (h * h)
def d3(F, x, h):
    return (F(x + 2.0 * h) - 2.0 * F(x + h) + 2.0 * F(x - h) - F(x - 2.0 * h)) / (2.0 * h ** 3)

def fricke_ratio(an, Q):
    fi = sum(an[n] * math.exp(-2.0 * math.pi * n) for n in range(1, 21))
    fiN = sum(an[n] * math.exp(-2.0 * math.pi * n / N) for n in range(1, Q + 1))
    return fiN / (N * fi), fi, fiN

if __name__ == "__main__":
    Q = 10000
    an = gen_a_n(Q)
    print("== 5077a1 (rank 3) y^2+y = x^3-7x+6, N=5077, eps=-1 ==")
    print("sample a_n n=1..20:", [an[n] for n in range(1, 21)])
    F = lambda s: F_L(s, an, Q)
    print("F(1) = L(1):", F(1.0), " (rank 3: should be ~0, eps=-1 forces it)")
    print("F'(1)  ~", d1(F, 1.0, 0.05))
    print("F''(1) ~", d2(F, 1.0, 0.2))
    print("L'''(1)/6 target 1.73184990 (Cremona ecdata);  L''' ~ 10.3911:")
    for h in (0.4, 0.2, 0.1, 0.05, 0.02, 0.01):
        print(f"  h={h:5.3f}  L'''/6 ~ {d3(F, 1.0, h) / 6.0:10.6f}")
    r, fi, fiN = fricke_ratio(an, Q)
    print(f"fricke: f(i/N)/(N*f(i)) = {r:+.6f}  (expect -1.00, eps_L=-1)")
    b = 2.0 * math.pi / SQN
    print(f"tail coefficient b = 2*pi/sqrt(5077) = {b:.6f}")
