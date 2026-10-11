# recon_10_01.py  (2026-10-11)
# (1,0)/(0,1)-type recon for the rank-1 exclusion layer on K = Q(sqrt 5).
# Root-number constraint:  eps(E^5) = eps(E) * chi_5(N).  To flip the parity we
# need chi_5(N) = -1  <=>  N ≡ ±2 (mod 5).  Then:
#   (1,0): rank(E)=1, eps(E)=-1 -> eps(E^5)=+1 (even rank); expect L(E^5,1) != 0
#   (0,1): rank(E)=0, eps(E)=+1 -> eps(E^5)=-1 (odd rank); expect L(E^5,1) ~ 0,
#          L'(E^5,1) != 0
# Same pure-stdlib pipeline as positivity_probe.py (Q=3000).
import math

GAMMA = 0.57721566490153286060651209008240243104215933593992

def primes_upto(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = b'\x00' * (((n - i*i) // i) + 1)
    return [i for i in range(2, n + 1) if sieve[i]]

def ap_modp(a1, a2, a3, a4, a6, p):
    if p == 2:
        cnt = 0
        for x in range(2):
            for y in range(2):
                lhs = (y * y + a1 * x * y + a3 * y) % 2
                rhs = (x ** 3 + a2 * x * x + a4 * x + a6) % 2
                if lhs == rhs:
                    cnt += 1
        return p - cnt
    tot = 0
    for x in range(p):
        R = (x ** 3 + a2 * x * x + a4 * x + a6) % p
        d = ((a1 * x + a3) * (a1 * x + a3) + 4 * R) % p
        if d == 0:
            tot += 1
        else:
            tot += 2 if pow(d, (p - 1) // 2, p) == 1 else 0
    return p - tot

def gen_a_n(Nmax, a1, a2, a3, a4, a6):
    primes = primes_upto(Nmax)
    ap = {p: ap_modp(a1, a2, a3, a4, a6, p) for p in primes}
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

def chi5(n):
    r = n % 5
    if r == 0:
        return 0
    return 1 if (r == 1 or r == 4) else -1

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

def probe(name, a1, a2, a3, a4, a6, N, epsE, rankE, Q):
    anE = gen_a_n(Q, a1, a2, a3, a4, a6)
    an5 = {n: chi5(n) * anE[n] for n in range(1, Q + 1)}
    N5 = 25 * N
    eps5 = epsE * chi5(N)
    f1 = F_L(1.0, an5, N5, eps5, Q)
    l1p = d1(F_L, 1.0, 0.02, an5, N5, eps5, Q)
    l1pp = d2(F_L, 1.0, 0.02, an5, N5, eps5, Q)
    if abs(f1) > 1e-6:
        r5 = 0
    elif abs(l1p) > 1e-6:
        r5 = 1
    else:
        r5 = 2
    # also L(E,1) over Q for the (0,1) candidates
    fE = F_L(1.0, anE, N, epsE, Q)
    print(f"{name:>6s} E rk={rankE} eps={epsE:+d} N={N:<4d} | chi5(N)={chi5(N):+d} "
          f"eps^5={eps5:+d} | L(E,1)={fE: .4f} | L(E^5,1)={f1: .3e}  L'(E^5,1)={l1p: .4f} "
          f"L''(E^5,1)={l1pp: .3e} => rk(E^5) ~ {r5}")
    return r5

def d2(F, s0, h, *a):
    return (F(s0 + h, *a) - 2 * F(s0, *a) + F(s0 - h, *a)) / (h * h)

def main():
    Q = 3000
    print("== (1,0)/(0,1) type recon on K = Q(sqrt 5), Q=%d ==" % Q)
    print("-- (1,0) candidates: rank-1 curves with N ≡ ±2 (mod 5) -> eps(E^5)=+1 --")
    c10 = [
        ("37a1", [0, 0, 1, -1, 0], 37, -1, 1),
        ("43a1", [0, 1, 1, 0, 0], 43, -1, 1),
        ("53a1", [1, 0, 1, -1, 1], 53, -1, 1),
        ("62a1", [0, -1, 1, 1, 0], 62, -1, 1),
    ]
    for name, co, N, eps, rk in c10:
        r5 = probe(name, *co, N, eps, rk, Q)
        print(f"    {'*** (1,0) REALIZED: rk(E)=1 and rk(E^5)=0' if r5 == 0 else ''}")
    print()
    print("-- (0,1) candidates: rank-0 curves with N ≡ ±2 (mod 5) -> eps(E^5)=-1 --")
    c01 = [
        ("17a1", [1, -1, 1, -1, 0], 17, 1, 0),
        ("27a1", [0, 0, 1, 0, 0], 27, 1, 0),
    ]
    for name, co, N, eps, rk in c01:
        r5 = probe(name, *co, N, eps, rk, Q)
        print(f"    {'*** (0,1) REALIZED: rk(E)=0 and rk(E^5)=1' if r5 == 1 else ''}")

if __name__ == "__main__":
    main()
