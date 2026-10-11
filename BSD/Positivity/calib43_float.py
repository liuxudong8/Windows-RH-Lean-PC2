# calib43_float.py — 43a1 (1,0) 闭证数值校准（float 版，2026-10-11）
# E = 43a1 : y^2 + xy + y = x^3 + x^2, N = 43, eps = -1, rank 1.
# E1(x) = int_x^inf e^-t/t dt：x<=2 用幂级数 E1(x) = -gamma - ln x - sum (-x)^k/(k*k!)
#        x>2  用渐近 e^-x/x * (1 - 1/x + 2/x^2 - 6/x^3 + ...)
# 产出：L'(43a1,1) 部分和/尾界；L(E^5,1) 部分和/尾界；Lean 表文件 aE_raw_43.lean、aE5_raw_43.lean
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

def chi5(p):
    r = p % 5
    return 0 if r == 0 else (1 if (r == 1 or r == 4) else -1)

def E1(x):
    if x <= 25:
        # power series: E1(x) = -gamma - ln x - sum_{k>=1} (-x)^k/(k*k!); converges
        # for all x>0; for x=25 the k=25 peak term is ~25^25/25! ~ 3e9 (float-safe)
        s = 0.0
        term = 1.0
        k = 1
        while True:
            term *= -x / k
            t = term / k
            s += t
            k += 1
            if k > 400 or abs(t) < 1e-20 * (1 + abs(s)):
                break
        return -GAMMA - math.log(x) - s
    # asymptotic e^-x/x * (1 - 1/x + 2!/x^2 - 3!/x^3 + ...), x large; stop at
    # first growing term (optimal truncation ~k=x)
    s = 1.0
    f = 1.0
    sign = -1.0
    k = 1
    xinv = 1.0 / x
    prev_t = 0.0
    while True:
        f *= k
        t = sign * f * (xinv ** (k + 1))
        if k > 1 and abs(t) > abs(prev_t):
            break
        s += t
        prev_t = t
        sign = -sign
        k += 1
        if k > 200:
            break
    return math.exp(-x) * s / x

# ---- tables ----
CO = (0, 1, 1, 0, 0)
N = 43
anE = gen_a_n(200, *CO)
an5 = {1: 1}
anE800 = gen_a_n(800, *CO)
for n in range(2, 801):
    an5[n] = chi5(n) * anE800[n] if (n % 5 != 0 and n % 43 != 0) else 0

with open(r"C:\proj2\BSD\aE_table_43.lean", "w") as f:
    f.write("-- auto-generated: a_n(E) first 200 terms, E = 43a1 (y^2+xy+y = x^3+x^2)\n")
    f.write("def aE_raw_43 : Nat -> Int\n")
    for n in range(0, 201):
        f.write(f"| {n} => {anE.get(n, 0)}\n")

with open(r"C:\proj2\BSD\aE5_table_43.lean", "w") as f:
    f.write("-- auto-generated: a_n(E^5) first 800 terms, E^5 = 43a1 twisted by chi_5\n")
    f.write("-- bad primes: 5 (additive), 43 (additive) -> a_n = 0 when 5|n or 43|n\n")
    f.write("def aE5_raw_43 : Nat -> Int\n")
    for n in range(0, 801):
        f.write(f"| {n} => {an5.get(n, 0)}\n")

print("tables written: aE_table_43.lean (200), aE5_table_43.lean (800)")

# ---- L'(43a1,1) ----
sqrt43 = math.sqrt(43)
def bn(n):
    return 2 * math.pi * n / sqrt43
l1 = 0.0
for n in range(1, 201):
    l1 += anE[n] * E1(bn(n)) / n
l1 = 2 * l1
print(f"\nsqrt43 = {sqrt43}")
print(f"b1 = {bn(1)}  (37a1's b1 = {2*math.pi/math.sqrt(37):.6f} for comparison)")
print(f"L'(43a1,1) ~ 2*S_200 = {l1:.15f}")

# partial sums
for Q in [10, 20, 30, 50, 100, 150]:
    s = 0.0
    for n in range(1, Q + 1):
        s += anE[n] * E1(bn(n)) / n
    print(f"  partial 2*S_{Q} = {2*s:.15f}")

# tail upper bound: 4 * sum_{n>Q} e^{-b(n)}/b(n)  (|a_n|<=2n, E1<=e^-b/b)
for Q in [10, 20, 30]:
    t = 0.0
    for n in range(Q + 1, 2000):
        t += math.exp(-bn(n)) / bn(n)
    print(f"  tail_{Q} <= 4*sum = {4*t:.3e}")

# ---- L(E^5,1), N^5 = 1075 ----
sqrt1075 = math.sqrt(1075)
alpha = 2 * math.pi / sqrt1075
print(f"\nalpha(1075) = {alpha}")
print(f"exp(-alpha) = {math.exp(-alpha)}")
L5 = 0.0
for n in range(1, 801):
    L5 += an5[n] * math.exp(-alpha * n) / n
L5 = 2 * L5
print(f"L(E^5,1) ~ 2*S_800 = {L5:.15f}")
for Q in [200, 400, 600, 800]:
    s = 0.0
    for n in range(1, Q + 1):
        s += an5[n] * math.exp(-alpha * n) / n
    print(f"  partial 2*S_{Q} = {2*s:.15f}")
# tail bound: |a_n|<=2 -> tail <= 2 * sum_{n>Q} e^{-alpha n}/n
for Q in [200, 400, 600, 800]:
    t = 0.0
    for n in range(Q + 1, 5000):
        t += math.exp(-alpha * n) / n
    print(f"  tail_{Q} <= 2*sum = {2*t:.3e}")

# sanity: recon value 4.891
print(f"\nrecon (Q=3000 pipeline) L(E^5,1) = 4.891e+00 -> consistent: {abs(L5 - 4.891) < 0.01}")
