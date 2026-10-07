# -*- coding: utf-8 -*-
"""Selmer FINAL3: fix ring_sub2 bug (was adding instead of subtracting for comps 1,2).
Full 64 candidates + explicit -theta. Basic units from wide scan kept as (9,-14,-5),(51,-59,-66).
"""
import sympy as sp
import mpmath as mp
import itertools
mp.mp.dps = 60

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

th1 = mp.findroot(lambda t: t**3 - 16*t + 16, 3.35)
th2 = mp.findroot(lambda t: t**3 - 16*t + 16, 1.08)
th3 = mp.findroot(lambda t: t**3 - 16*t + 16, -4.43)
ths = [th1, th2, th3]
pis = [t/2 for t in ths]
def conj(cvec):
    X0, X1, X2 = cvec
    return [X0 + X1*p + X2*p*p for p in pis]

eta1 = (9, -14, -5); eta2 = (51, -59, -66)
one = (1, 0, 0); neg1 = (-1, 0, 0)
th3el = (3, 2, 0); p37_2 = (-41, -3, 7); pi_el = (0, 1, 0)

prime_part = []
for bits in range(8):
    acc = one
    if bits & 1: acc = mul(acc, pi_el)
    if bits & 2: acc = mul(acc, th3el)
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
def is_sq_rat(n):
    if n < 0: return False
    r = mp.sqrt(mp.mpf(n))
    return abs(r - mp.nint(r)) < mp.mpf('1e-40')
selN = [t for t in cands if is_sq_rat(t[5])]
print("candidates:", len(cands), "N-filter:", len(selN))

K2 = 14; M2 = 2**K2
def ring_mul2(a, b):
    A0, A1, A2 = a; B0, B1, B2 = b
    c0 = A0*B0; c1 = A0*B1 + A1*B0; c2 = A0*B2 + A1*B1 + A2*B0
    c3 = A1*B2 + A2*B1; c4 = A2*B2
    return ((c0 - 2*c3) % M2, (c1 + 4*c3 - 2*c4) % M2, (c2 + 4*c4) % M2)
def ring_add2(a, b):
    return ((a[0]+b[0]) % M2, (a[1]+b[1]) % M2, (a[2]+b[2]) % M2)
def ring_sub2(a, b):
    return ((a[0]-b[0]) % M2, (a[1]-b[1]) % M2, (a[2]-b[2]) % M2)   # FIXED
print("2-adic ring ...")
pow2 = [(1, 0, 0)]
pi = (0, 1, 0)
for i in range(1, K2):
    pow2.append(ring_mul2(pow2[-1], pi))
elems2 = set()
for bits in range(M2):
    acc = (0, 0, 0)
    b_ = bits; i = 0
    while b_:
        if b_ & 1:
            acc = ring_add2(acc, pow2[i])
        b_ >>= 1; i += 1
    elems2.add(acc)
assert len(elems2) == M2
sq2 = { ring_mul2(e, e) for e in elems2 }
print("sq2:", len(sq2))

def local_p2(xi, detail=False):
    X0, X1, X2 = [v % M2 for v in xi]
    xi_el = (X0, X1, X2)
    sixteen = (16 % M2, 0, 0)
    def fval(X):
        xx3 = ring_mul2(ring_mul2(X, X), X)
        return ring_add2(ring_sub2(xx3, ring_mul2(sixteen, X)), sixteen)
    for w in range(14):
        pw = pow2[w]
        for e in elems2:
            if ring_mul2(xi_el, fval(ring_mul2(pw, e))) in sq2:
                if detail: print(f"    p2 hit w={w} e={e}")
                return True
    for t in elems2:
        t2 = ring_mul2(t, t); t3 = ring_mul2(t2, t)
        g = ring_add2(ring_sub2((1 % M2, 0, 0), ring_mul2(sixteen, t2)), ring_mul2(sixteen, t3))
        if ring_mul2(xi_el, g) in sq2:
            if detail: print(f"    p2 hit infinity t={t}")
            return True
    return False

K37 = 4; M37 = 37**K37
print("37-adic ring ...")
sq37 = { (zz*zz) % M37 for zz in range(M37) }
def v37(n):
    v = 0
    while n % 37 == 0 and n != 0:
        n //= 37; v += 1
    return v

def local_p37(xi, pi_r):
    X0, X1, X2 = xi
    pr2 = (pi_r * pi_r) % M37
    xi_img = (X0 + X1*pi_r + X2*pr2) % M37
    def fint(X):
        return (X**3 - 16*X + 16) % M37
    for xx in range(M37):
        c = (xi_img * fint(xx)) % M37
        if c == 0:
            x8 = xx % (37**8)
            pr8 = pi_r % (37**8)
            xi8 = (X0 + X1*pr8 + X2*(pr8*pr8 % (37**8))) % (37**8)
            c8 = (xi8 * ((x8**3 - 16*x8 + 16) % (37**8))) % (37**8)
            v = v37(c8)
            if v % 2 == 1:
                continue
            pw = 8 - v
            u2 = (c8 // (37**v)) % (37**pw)
            if any((w*w) % (37**pw) == u2 for w in range(37**pw)):
                return True
        elif c in sq37:
            return True
    for t in range(M37):
        g = (1 - 16*t*t + 16*t*t*t) % M37
        c = (xi_img * g) % M37
        if c == 0:
            t8 = t % (37**8)
            g8 = (1 - 16*t8*t8 + 16*t8*t8*t8) % (37**8)
            pr8 = pi_r % (37**8)
            xi8 = (X0 + X1*pr8 + X2*(pr8*pr8 % (37**8))) % (37**8)
            c8 = (xi8 * g8) % (37**8)
            v = v37(c8)
            if v % 2 == 1:
                continue
            pw = 8 - v
            u2 = (c8 // (37**v)) % (37**pw)
            if any((w*w) % (37**pw) == u2 for w in range(37**pw)):
                return True
        elif c in sq37:
            return True
    return False

neg_theta = (0, -2, 0)
print("\n=== local solubility (final3) ===")
selmer = []
for (pb, ua, ub, us, c, Nv) in selN:
    l1 = local_p37(c, 17); l2 = local_p37(c, 10); lp = local_p2(c)
    ok = l1 and l2 and lp
    if ok: selmer.append(c)
    print(f"pb={pb} ua={ua} ub={ub} us={us:+d} xi={c} N={Nv}: p37_1={l1} p37_2={l2} p2={lp} -> {'SELMER' if ok else 'no'}")
l1 = local_p37(neg_theta, 17); l2 = local_p37(neg_theta, 10); lp = local_p2(neg_theta, detail=True)
print(f"EXPLICIT -theta=(0,-2,0) N=16: p37_1={l1} p37_2={l2} p2={lp} -> {'SELMER' if l1 and l2 and lp else 'no'}")
if l1 and l2 and lp:
    selmer.append(neg_theta)
print("\n|Sel^2| =", len(selmer))
for c in selmer:
    print("   ", c, "N =", nrm(*c))
