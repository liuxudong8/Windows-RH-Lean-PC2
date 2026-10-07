# -*- coding: utf-8 -*-
"""Selmer 2-descent COMPLETE coverage.
E' = 37a1: y^2 = x^3 - 16x + 16, no Q-torsion.
K = Q(theta) root field, O_K = Z[pi], pi = theta/2.
K(S,2): S = {p2, p37_1, p37_2}, dim 5 (3 prime + 2 unit-rank).
We build FULL candidate set: prime part 2^3 x unit part 8 (signed) = 64 classes.
Basic units found by minimal |log-det| pair among N=+-1 solutions.
"""
import sympy as sp
import mpmath as mp
import itertools
mp.mp.dps = 60

# ---------- norm form ----------
x, y, z = sp.symbols('x y z')
M = sp.Matrix([
    [x, -2*z, -2*y],
    [y, x + 4*z, 4*y - 2*z],
    [z, y, x + 4*z],
])
Nm = sp.expand(M.det())
poly = sp.Poly(Nm, x, y, z)
coefs = {}
for mon, c in poly.terms():
    coefs[tuple(mon)] = int(c)

def nrm(X, Y, Z):
    return sum(c * X**dx * Y**dy * Z**dz for (dx, dy, dz), c in coefs.items())

def mul(a, b):
    A0, A1, A2 = a; B0, B1, B2 = b
    c0 = A0*B0; c1 = A0*B1 + A1*B0; c2 = A0*B2 + A1*B1 + A2*B0
    c3 = A1*B2 + A2*B1; c4 = A2*B2
    return (c0 - 2*c3, c1 + 4*c3 - 2*c4, c2 + 4*c4)

# ---------- theta roots & embeddings ----------
th1 = mp.findroot(lambda t: t**3 - 16*t + 16, 3.35)
th2 = mp.findroot(lambda t: t**3 - 16*t + 16, 1.08)
th3 = mp.findroot(lambda t: t**3 - 16*t + 16, -4.43)
ths = [th1, th2, th3]
pis = [t/2 for t in ths]

def conj(cvec):
    X0, X1, X2 = cvec
    return [X0 + X1*p + X2*p*p for p in pis]

# ---------- basic units: minimal |log-det| pair among N=+-1 ----------
units_c = []
for X in range(-60, 61):
    for Y in range(-60, 61):
        for Z in range(-60, 61):
            if abs(nrm(X, Y, Z)) == 1:
                units_c.append((X, Y, Z))

best = None
for a, b in itertools.combinations(units_c, 2):
    la = [mp.log(mp.fabs(t)) for t in conj(a)]
    lb = [mp.log(mp.fabs(t)) for t in conj(b)]
    # 2x2 det dropping 3rd coord (log|N|=0 => any two rows fine)
    d = la[0]*lb[1] - la[1]*lb[0]
    if mp.fabs(d) > mp.mpf('1e-6'):
        ad = mp.fabs(d)
        if best is None or ad < best[0]:
            best = (ad, a, b)
print("basic unit pair (min |log-det|):", best[1], "N=", nrm(*best[1]), "|", best[2], "N=", nrm(*best[2]), "det=", mp.nstr(best[0], 8))
eta1, eta2 = best[1], best[2]
# ensure independent classes (mod squares): just proceed; pairs with det=R give d=1

# ---------- full candidate set: 64 ----------
one = (1, 0, 0)
neg1 = (-1, 0, 0)
th3 = (3, 2, 0)           # p37_1, N=37
p37_2 = (-41, -3, 7)      # p37_2 rep, N=-37
pi_el = (0, 1, 0)

prime_part = []
for bits in range(8):
    acc = one
    if bits & 1: acc = mul(acc, pi_el)
    if bits & 2: acc = mul(acc, th3)
    if bits & 4: acc = mul(acc, p37_2)
    prime_part.append((bits, acc))

unit_part = []
for a in (0, 1):
    for b in (0, 1):
        for s in (1, -1):
            acc = one
            if a: acc = mul(acc, eta1)
            if b: acc = mul(acc, eta2)
            if s == -1: acc = mul(acc, neg1)
            unit_part.append((a, b, s, acc))

cands = []
for (pb, pp), (ua, ub, us, up) in itertools.product(prime_part, unit_part):
    c = mul(pp, up)
    cands.append((pb, ua, ub, us, c, nrm(*c)))
print("total candidates:", len(cands))

# N in Q*^2 filter
def is_sq_rat(n):
    if n < 0: return False
    r = mp.sqrt(mp.mpf(n))
    return abs(r - mp.nint(r)) < mp.mpf('1e-40')

selN = [(pb, ua, ub, us, c, Nv) for (pb, ua, ub, us, c, Nv) in cands if is_sq_rat(Nv)]
print("after N-filter:", len(selN))
for t in selN[:20]:
    print("   pb=%d ua=%d ub=%d us=%+d N=%d" % (t[0], t[1], t[2], t[3], t[5]))

# ---------- local solubility ----------
def ring_mul8(a, b):
    A0, A1, A2 = a; B0, B1, B2 = b
    c0 = A0*B0; c1 = A0*B1 + A1*B0; c2 = A0*B2 + A1*B1 + A2*B0
    c3 = A1*B2 + A2*B1; c4 = A2*B2
    m = 2**8
    return ((c0 - 2*c3) % m, (c1 + 4*c3 - 2*c4) % m, (c2 + 4*c4) % m)

def ring_add8(a, b):
    m = 2**8
    return ((a[0]+b[0]) % m, (a[1]+b[1]) % m, (a[2]+b[2]) % m)

def ring_sub8(a, b):
    m = 2**8
    return ((a[0]-b[0]) % m, (a[1]+b[1]) % m, (a[2]+b[2]) % m)

def ring_elems8():
    m = 2**8
    powers = [(1, 0, 0)]
    pi = (0, 1, 0)
    for i in range(1, 8):
        powers.append(ring_mul8(powers[-1], pi))
    elems = set()
    for bits in range(2**8):
        acc = (0, 0, 0)
        for i in range(8):
            if bits >> i & 1:
                acc = ring_add8(acc, powers[i])
        elems.add(acc)
    assert len(elems) == 2**8
    return elems

def local_p2(xi):
    elems = ring_elems8()
    sq = { ring_mul8(e, e) for e in elems }
    m = 2**8
    X0, X1, X2 = [v % m for v in xi]
    xi_el = (X0, X1, X2)
    sixteen = (16 % m, 0, 0)
    def fval(X):
        xx3 = ring_mul8(ring_mul8(X, X), X)
        return ring_add8(ring_sub8(xx3, ring_mul8(sixteen, X)), sixteen)
    powers = [(1, 0, 0)]
    pi = (0, 1, 0)
    for i in range(1, 8):
        powers.append(ring_mul8(powers[-1], pi))
    for w in (0, 2, 4, 6):
        pw = powers[w]
        for e in elems:
            c = ring_mul8(xi_el, fval(ring_mul8(pw, e)))
            if c in sq:
                return True
    for t in elems:
        t2 = ring_mul8(t, t); t3 = ring_mul8(t2, t)
        g = ring_add8(ring_sub8((1 % m, 0, 0), ring_mul8(sixteen, t2)), ring_mul8(sixteen, t3))
        if ring_mul8(xi_el, g) in sq:
            return True
    return False

def local_p37(xi, pi_r, k=2):
    p = 37; p2 = p**k
    sq = { (zz*zz) % p2 for zz in range(p2) }
    X0, X1, X2 = xi
    xi_img = (X0 + X1*pi_r + X2*(pi_r*pi_r % p2)) % p2
    def fint(X):
        return (X**3 - 16*X + 16) % p2
    for xx in range(p2):
        if (xi_img * fint(xx)) % p2 in sq:
            return True
    for t in range(p2):
        g = (1 - 16*t*t + 16*t*t*t) % p2
        if (xi_img * g) % p2 in sq:
            return True
    return False

print("\n=== local solubility on N-filtered candidates ===")
selmer = []
for (pb, ua, ub, us, c, Nv) in selN:
    l1 = local_p37(c, 17)   # p37_1: theta=34, pi=17
    l2 = local_p37(c, 10)   # p37_2: theta=20, pi=10
    lp = local_p2(c)
    ok = l1 and l2 and lp
    if ok:
        selmer.append(c)
    print(f"pb={pb} ua={ua} ub={ub} us={us:+d} xi={c} N={Nv}: p37_1={l1} p37_2={l2} p2={lp} -> {'SELMER' if ok else 'no'}")

print("\n=== Sel^2(E/Q) FULL === |Sel^2| =", len(selmer))
for c in selmer:
    print("   ", c, "N =", nrm(*c))
print("expect {1=(1,0,0), -theta=(0,-2,0)}")
print("dim Sel^2 =", len(selmer) and int(mp.log(len(selmer), 2)) or 0, "=> rank E(Q) <=", len(selmer) and int(mp.log(len(selmer), 2)) or 0)
