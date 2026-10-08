# positivity_probe.py  (Stage3 P* data recon: ①)
# Decide (1,1)-type existence in the Artin decomposition  L(E/K) = L(E)*L(E^5)
# for K = Q(sqrt 5).  (1,1)-type = ord L(E) = 1 AND ord L(E^5) = 1, where
# E^5 is the quadratic twist by chi_5 (Kronecker character mod 5).
#
# Tools:
#   a_n(E^5) = chi_5(n) * a_n(E)      (chi_5: 1,4 -> +1 ; 2,3 -> -1 ; 5|n -> 0)
#   N(E^5)   = 25 * N(E)              (gcd(N(E),5)=1 for all candidates here)
#   eps(E^5) = eps(E) * chi_5(N(E))
# Analytic rank of E^5 read off F(1)=L(E^5,1) (+ first derivative when needed).
# Rank-1 curves with N ≡ ±1 mod 5 give eps(E^5) = -1 (odd rank allowed): those
# are the only candidates that can realize (1,1).  389a1 (rank 2, eps=+1) is
# probed too: its E^5 has eps=+1 (even rank), distinguishing (2,0) vs (2,2).
#
# Pure stdlib; same convergent framework as probe389/5077 (fixed S2' form).
import math

GAMMA = 0.57721566490153286060651209008240243104215933593992

def primes_upto(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = b'\x00' * (((n - i*i) // i) + 1)
    return [i for i in range(2, n + 1) if sieve[i]]

# ---- point counting on E: y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6 ----
# a_p = p + 1 - #E(F_p) = p - #affine    (valid for bad primes too:
#   additive -> #E=p+1 -> a_p=0 ; split mult -> #E=p -> a_p=1 ; non-split -> a_p=-1)
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

# ---- chi_5 (Kronecker (n/5)): 1,4 -> +1 ; 2,3 -> -1 ; 5|n -> 0 ----
def chi5(n):
    r = n % 5
    if r == 0:
        return 0
    return 1 if (r == 1 or r == 4) else -1

# ---- upper incomplete Gamma (same as probe389) ----
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

# ---- convergent L value: F(s) = S1(s) + C(s) * S2'(s) / epsL ----
# (S2' must NOT be divided by Gamma(2-s): fixed in probe5077 round)
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

# ---- probe one curve: E (Q) -> E^5 (twist), report L(E^5,1), L'(E^5,1) ----
def probe_twist(name, a1, a2, a3, a4, a6, N, epsE, rankE, Q):
    anE = gen_a_n(Q, a1, a2, a3, a4, a6)
    # twist coefficients
    an5 = {n: chi5(n) * anE[n] for n in range(1, Q + 1)}
    N5 = 25 * N
    eps5 = epsE * chi5(N)            # chi_5(N): sign of eps(E^5) = eps(E)*chi_5(N)
    f1 = F_L(1.0, an5, N5, eps5, Q)
    l1p = d1(F_L, 1.0, 0.02, an5, N5, eps5, Q)
    l1pp = d2(F_L, 1.0, 0.02, an5, N5, eps5, Q)
    # rank decision
    if abs(f1) > 1e-6:
        r5 = 0
    elif abs(l1p) > 1e-6:
        r5 = 1
    else:
        r5 = 2
    print(f"{name:>8s}  E: rank={rankE} eps={epsE:+d} N={N:<5d} "
          f"| E^5: eps^5={eps5:+d} N^5={N5:<6d} "
          f"L(E^5,1)={f1: .3e}  L'(E^5,1)={l1p: .3e}  L''(E^5,1)={l1pp: .3e}  => rk(E^5) ~ {r5}")
    return r5, f1, l1p

def main():
    Q = 3000
    print("== (1,1)-type existence recon on K = Q(sqrt 5) ==  (Q=%d)" % Q)
    print("Rank-1 candidates with N ≡ ±1 (mod 5): eps(E^5) = -1, odd rank allowed.")
    print()
    cands = [
        # (name, [a1,a2,a3,a4,a6], N, eps(E), rank(E)   -- rank from allbsd)
        ("79a1",  [1, 1, 1, -2, 0], 79,  -1, 1),
        ("89a1",  [1, 1, 1, -1, 0], 89,  -1, 1),
        ("91a1",  [0, 0, 1, 1, 0], 91,  -1, 1),
        ("99a1",  [1, -1, 1, -2, 0], 99, -1, 1),
        ("101a1", [0, 1, 1, -1, -1], 101, -1, 1),
        ("106b1", [1, 1, 0, -7, 5], 106, -1, 1),
    ]
    hits = 0
    print("-- twist probe: L(E^5,1), L'(E^5,1) --")
    for name, co, N, eps, rk in cands:
        r5, f1, l1p = probe_twist(name, *co, N, eps, rk, Q)
        if r5 == 1:
            hits += 1
            print(f"    *** (1,1)-TYPE REALIZED: {name} has rk(E)=1 and rk(E^5)=1")
    print()
    print(f"== (1,1)-type hits: {hits} / {len(cands)} ==")
    print()
    # entanglement sign law: L'(E,1) * L'(E^5,1) > 0 for every (1,1) candidate
    print("-- entanglement sign probe: L'(E,1) (over Q, eps=-1 rank-1) vs L'(E^5,1) --")
    for name, co, N, eps, rk in cands:
        a1, a2, a3, a4, a6 = co
        anE = gen_a_n(Q, a1, a2, a3, a4, a6)
        an5 = {n: chi5(n) * anE[n] for n in range(1, Q + 1)}
        N5 = 25 * N
        eps5 = eps * chi5(N)
        l1pE = d1(F_L, 1.0, 0.02, anE, N, eps, Q)
        l1pE5 = d1(F_L, 1.0, 0.02, an5, N5, eps5, Q)
        sign = "+" if l1pE * l1pE5 > 0 else "-"
        print(f"{name:>8s}  L'(E,1)={l1pE: .4f}   L'(E^5,1)={l1pE5: .4f}   product>0? {sign}")
    print()
    # 389a1 itself: rank 2, eps +1 -> eps(E^5) = +1*chi_5(389) = +1 (even rank)
    print("== 389a1: E rank 2 (allbsd), eps=+1, N=389 ≡ 4 (mod 5) => eps(E^5)=+1 ==")
    probe_twist("389a1", 0, 1, 1, -2, 0, 389, 1, 2, Q)

if __name__ == "__main__":
    main()
