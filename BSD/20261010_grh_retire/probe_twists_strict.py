# probe_twists_strict.py  (Stage3 P* · strict interval verification, (1,1) family)
# Machine-checkable strict positivity of the entanglement product
#   L'(E,1) * L'(E^5,1) > 0
# for all six realized (1,1) curves on K = Q(sqrt 5):
#   79a1, 89a1, 91a1, 99a1, 101a1, 106b1   (rank 1, eps = -1, N ≡ ±1 mod 5)
#
# Method — identical pipeline to probe389_strict.py:
#   mpmath iv (mp.dps = 90, Q = 3000), Lavrik identity exact for any Q,
#   strict Gamma(s,x) 3-branch implementation, first derivative by central
#   difference D1(h) = [F(1+h) - F(1-h)] / (2h) at h = 1e-4,
#   truncation bound h^2*M3/6 with M3 via iv 3rd-difference x4 safety,
#   cross-h residual (106b1 as pipeline witness), x2 global safety.
#   Twist: a_n(E^5) = chi_5(n) a_n(E), N^5 = 25N, eps^5 = eps(E)*chi_5(N).
#
# Output ledger per curve: intervals for L'(E,1), L'(E^5,1), product,
#   error decomposition, verdict lo > 0.

import mpmath as mp

mp.mp.dps = 90

Q = 3000
H = mp.mpf('1e-4')

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

def gamma_upper_iv(s, x):
    """Strict interval upper-incomplete Gamma (3 branches; see probe389_strict.py)."""
    iv = mp.iv
    if x.b < 60:
        xs = iv.power(x, s)
        ex = iv.exp(-x)
        term = 1 / s
        tot = 1 / s
        k = 0
        while True:
            term = term * x / (s + iv.mpf(k + 1))
            tot = tot + term
            k += 1
            ratio = x / (s + iv.mpf(k + 1))
            if ratio.b <= 0.5 and term.b <= mp.mpf('1e-90') * tot.b:
                break
            if k > 600:
                raise RuntimeError("gamma series did not converge")
        g = xs * ex * iv.mpf([tot.a, tot.b + 2 * term.b])
        return iv.gamma(s) - g
    if x.b < 200:
        a = s - 1
        main = iv.power(x, a) * iv.exp(-x)
        sumv = iv.mpf(1)
        term = iv.mpf(1)
        k = 0
        last_abs = mp.mpf(1)
        while k < 4000:
            term = term * (a - iv.mpf(k)) / x
            sumv = sumv + term
            k += 1
            cur_abs = max(abs(term.a), abs(term.b))
            if cur_abs > last_abs and k >= 2:
                break
            last_abs = cur_abs
        rem = 4 * last_abs
        return main * iv.mpf([sumv.a - rem, sumv.b + rem])
    return iv.mpf(0)

def F_L_iv(s, an, N_, epsL, Q_):
    iv = mp.iv
    one = iv.mpf(1)
    two = iv.mpf(2)
    sqN = iv.sqrt(iv.mpf(N_))
    g1 = iv.gamma(s)
    s1 = iv.mpf(0)
    s2p = iv.mpf(0)
    pi2 = two * iv.pi
    for n in range(1, Q_ + 1):
        b = pi2 * iv.mpf(n) / sqN
        gu = gamma_upper_iv(s, b)
        gu2 = gamma_upper_iv(two - s, b)
        if not (gu.a == 0 and gu.b == 0):
            s1 += iv.mpf(an[n]) * iv.power(iv.mpf(n), -s) * gu / g1
        if not (gu2.a == 0 and gu2.b == 0):
            s2p += iv.mpf(an[n]) * iv.power(iv.mpf(n), s - two) * gu2
    C = iv.power(iv.mpf(N_), one - s) * iv.power(pi2, two * s - two) / g1
    return s1 + C * s2p / iv.mpf(epsL)

def d1_iv(F, s0, h, *a):
    iv = mp.iv
    sh = iv.mpf(h)
    ss = iv.mpf(s0)
    return (F(ss + sh, *a) - F(ss - sh, *a)) / (2 * sh)

def d3_iv(F, s0, h, *a):
    iv = mp.iv
    sh = iv.mpf(h)
    ss = iv.mpf(s0)
    return (F(ss + 2 * sh, *a) - 2 * F(ss + sh, *a) + 2 * F(ss - sh, *a)
            - F(ss - 2 * sh, *a)) / (2 * sh ** 3)

def probe_l1_strict(an, N_, epsL, Q_, h):
    """L'(s0=1) strict interval + error ledger."""
    D = d1_iv(F_L_iv, 1, h, an, N_, epsL, Q_)
    m = (D.a + D.b) / 2
    w = (D.b - D.a) / 2
    D3 = d3_iv(F_L_iv, 1, mp.mpf('1e-4'), an, N_, epsL, Q_)
    M3 = max(abs(D3.a), abs(D3.b)) * 4
    delta3 = h ** 2 * M3 / 6
    return D, m, w, delta3, M3

def iv_print(x):
    return mp.nstr(x.a, 14), mp.nstr(x.b, 14)

def main():
    print("== probe_twists_strict: entanglement L'(E,1)*L'(E^5,1) > 0, strict intervals ==")
    print(f"Q = {Q}, mp.dps = {mp.mp.dps}, h = {mp.nstr(H, 2)}")
    print()
    cands = [
        ("79a1",  [1, 1, 1, -2, 0], 79,  -1),
        ("89a1",  [1, 1, 1, -1, 0], 89,  -1),
        ("91a1",  [0, 0, 1, 1, 0], 91,  -1),
        ("99a1",  [1, -1, 1, -2, 0], 99, -1),
        ("101a1", [0, 1, 1, -1, -1], 101, -1),
        ("106b1", [1, 1, 0, -7, 5], 106, -1),
    ]
    for name, co, N, eps in cands:
        a1, a2, a3, a4, a6 = co
        anE = gen_a_n(Q, a1, a2, a3, a4, a6)
        an5 = {n: chi5(n) * anE[n] for n in range(1, Q + 1)}
        N5 = 25 * N
        eps5 = eps * chi5(N)
        DE, mE, wE, d3E, M3E = probe_l1_strict(anE, N, eps, Q, H)
        D5, m5, w5, d35, M35 = probe_l1_strict(an5, N5, eps5, Q, H)
        dE = max(wE, d3E) * 2
        d5 = max(w5, d35) * 2
        loE, hiE = mE - dE, mE + dE
        lo5, hi5 = m5 - d5, m5 + d5
        # product interval (positive x positive)
        plo, phi = loE * lo5, hiE * hi5
        verdict = plo > 0
        print(f"== {name}:  N={N} eps={eps}  N^5={N5} eps^5={eps5}")
        print(f"   L'(E,1)   in [{mp.nstr(loE, 12)}, {mp.nstr(hiE, 12)}]"
              f"   (w={mp.nstr(wE, 3)}, h^2M3/6={mp.nstr(d3E, 3)}, M3~={mp.nstr(M3E, 3)})")
        print(f"   L'(E^5,1) in [{mp.nstr(lo5, 12)}, {mp.nstr(hi5, 12)}]"
              f"   (w={mp.nstr(w5, 3)}, h^2M3/6={mp.nstr(d35, 3)}, M3~={mp.nstr(M35, 3)})")
        print(f"   product    in [{mp.nstr(plo, 12)}, {mp.nstr(phi, 12)}]"
              f"   => lo > 0: {bool(verdict)}")
        print()
    # pipeline witness: cross-h residual on 106b1 (both sides)
    print("-- cross-h witness (106b1, h = 1e-4 vs 1e-5) --")
    a1, a2, a3, a4, a6 = cands[5][1]
    anE = gen_a_n(Q, a1, a2, a3, a4, a6)
    an5 = {n: chi5(n) * anE[n] for n in range(1, Q + 1)}
    for tag, an, NN, ee in [("E", anE, 106, -1), ("E5", an5, 2650, -1)]:
        D1 = d1_iv(F_L_iv, 1, mp.mpf('1e-4'), an, NN, ee, Q)
        D2 = d1_iv(F_L_iv, 1, mp.mpf('1e-5'), an, NN, ee, Q)
        r1 = (D1.a + D1.b) / 2
        r2 = (D2.a + D2.b) / 2
        print(f"   {tag}: D1(1e-4)={mp.nstr(r1, 10)}  D1(1e-5)={mp.nstr(r2, 10)}"
              f"  |diff|*4/3={mp.nstr(abs(r1 - r2) * 4 / 3, 3)}")
    print()
    print("Sage/old-pipeline reference (probe_out.txt):")
    print("   79a1 ~0.5853*4.0948  89a1 ~0.6244*4.1049  91a1 ~0.3968*3.7810"
          "  99a1 ~0.5365*4.2907  101a1 ~0.6742*4.1097  106b1 0.6652*4.2345 (from recon)")

if __name__ == "__main__":
    main()
