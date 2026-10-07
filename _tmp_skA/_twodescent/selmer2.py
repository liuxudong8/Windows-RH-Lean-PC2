# -*- coding: utf-8 -*-
"""Selmer 2-descent (fixed): E' = 37a1, y^2 = f(x) = x^3-16x+16, no Q-torsion.
K = Q(theta), f = minpoly of theta.  delta: E(Q)/2 -> K(S,2), delta(P) = x(P) - theta.
delta(P0) = -theta.  Need: (a) class of -theta among signed unit classes;
(b) full local solubility incl. negative-valuation & infinity patches;
(c) |Sel^2(E/Q)| = 2 (dim 1) => rank E(Q) <= 1.
"""
import sympy as sp
import mpmath as mp
mp.mp.dps = 60

# ---------- K arithmetic ----------
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

# theta roots (real): f(x) = x^3 - 16x + 16
th1 = mp.findroot(lambda t: t**3 - 16*t + 16, 3.35)
th2 = mp.findroot(lambda t: t**3 - 16*t + 16, 1.12)
th3 = mp.findroot(lambda t: t**3 - 16*t + 16, -4.47)
ths = [th1, th2, th3]
print("roots:", [mp.nstr(t, 20) for t in ths])

# pi = theta/2 conjugates
pis = [t/2 for t in ths]

def conj(cvec):
    """3 embeddings of a+ b pi + c pi^2"""
    X0, X1, X2 = cvec
    return [X0 + X1*p + X2*p*p for p in pis]

# units
e1 = (-73, -5, 29)   # N = -1
e2 = (-71, 10, 19)   # N = +1
print("N(e1), N(e2):", nrm(*e1), nrm(*e2))

# u = (4 - pi^2)/pi^2  (unit, N = -1);  -theta = -2pi  (N = 16)
u = mul((4, 0, -1), (0, -2, 0))  # (4-pi^2) * pi^{-2}? pi^{-2} not in basis...
# compute u directly: u = 4/pi^2 - 1  as element? avoid; work with -theta directly.
# -theta = (0,-2,0); find (a,b,s): -theta * (s e1^a e2^b)  square?
def sq_class_check(w):
    """return (all_valuations_even_and_positive?) via: w square <=> all conj > 0
    and log(w)/2 in unit log lattice (numeric)."""
    wc = conj(w)
    if any(t.real <= 0 for t in wc):
        return False
    lw = [mp.log(mp.fabs(t)) for t in wc]
    return lw  # return logs for lattice check

# lattice basis: e1, e2 logs (drop 3rd coord)
le1 = [mp.log(mp.fabs(t)) for t in conj(e1)]
le2 = [mp.log(mp.fabs(t)) for t in conj(e2)]
print("logs e1:", [mp.nstr(t, 6) for t in le1])
print("logs e2:", [mp.nstr(t, 6) for t in le2])
# det (drop 3rd)
G = mp.matrix([[le1[0], le2[0]], [le1[1], le2[1]]])

def lattice_solve(lv):
    """lv 2-vector -> coordinates in (e1,e2) 2D basis"""
    b = mp.matrix([lv[0], lv[1]])
    return mp.lu_solve(G, b)

neg_theta = (0, -2, 0)
print("\n=== class of -theta among signed unit classes ===")
found = None
for a in (0, 1):
    for b in (0, 1):
        for s in (1, -1):
            base = (1, 0, 0)
            if a: base = mul(base, e1)
            if b: base = mul(base, e2)
            if s == -1: base = mul(base, (-1, 0, 0))
            w = mul(neg_theta, base)  # -theta * class (we test if product is square:
            # actually want: is -theta == class * square  <=>  -theta/class = -theta*class (class^2=1) is square
            wc = conj(w)
            if any(mp.fabs(t.real) <= mp.mpf('1e-40') for t in wc):
                tag = "ZERO-conj"
            elif all(t.real > 0 for t in wc):
                lw = [mp.log(t) for t in wc]
                c = lattice_solve(lw)  # need lw/2 in lattice
                c2 = (c[0]/2, c[1]/2)
                r = max(abs(c2[0] - mp.nint(c2[0])), abs(c2[1] - mp.nint(c2[1])))
                tag = f"all-pos, coords/2={mp.nstr(c2[0],4)},{mp.nstr(c2[1],4)} round-err={mp.nstr(r,3)}"
                if r < mp.mpf('1e-8'):
                    tag += "  <-- SQUARE"
            else:
                tag = "not all pos"
            print(f"a={a} b={b} s={s:+d}: w=-theta*class: {tag}")
            if 'SQUARE' in tag:
                found = (a, b, s)
print("=> -theta class =", found, "=> -theta =", f"(-1)^0 e1^{found[0]} e2^{found[1]} * sign {found[2]}" if found else "???")

# u = (4-pi^2)/pi^2: element = (4,0,-1) * pi^{-2}; pi^{-2} = ? 2 = pi(4-pi^2) => pi^{-1} = (4-pi^2)/2
# pi^{-2} = (4-pi^2)^2 / 4 ; u = (4-pi^2)^3 / 4  -- messy; skip, use -theta directly.
print("\nN(-theta) =", nrm(*neg_theta), "(should be 16)")

# ---------- local solubility with negative-valuation + infinity patches ----------
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
    return ((a[0]-b[0]) % m, (a[1]-b[1]) % m, (a[2]-b[2]) % m)

def ring_elems8():
    m = 2**8
    one = (1, 0, 0); pi = (0, 1, 0)
    powers = [(1, 0, 0)]
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
    # patches: x = pi^w * e, w in {0,2,4,6}
    pis = [(1,0,0)]
    pi = (0, 1, 0)
    for i in range(1, 8):
        pis.append(ring_mul8(pis[-1], pi))
    for w in (0, 2, 4, 6):
        pw = pis[w]
        for e in elems:
            xval = ring_mul8(pw, e)
            c = ring_mul8(xi_el, fval(xval))
            if c in sq:
                return True
    # infinity patch: t in ring, z'^2 = xi*(1 - 16 t^2 + 16 t^3)
    for t in elems:
        t2 = ring_mul8(t, t); t3 = ring_mul8(t2, t)
        g = ring_add8(ring_sub8((1 % m,0,0), ring_mul8(sixteen, t2)), ring_mul8(sixteen, t3))
        c = ring_mul8(xi_el, g)
        if c in sq:
            return True
    return False

def local_p37(xi, theta_r, pi_r, k=2):
    p = 37; p2 = p**k
    sq = { (zz*zz) % p2 for zz in range(p2) }
    X0, X1, X2 = xi
    xi_img = (X0 + X1*pi_r + X2*(pi_r*pi_r % p2)) % p2
    def fint(X):
        return (X**3 - 16*X + 16) % p2
    # affine patch: x in Z/p^k
    for xx in range(p2):
        c = (xi_img * fint(xx)) % p2
        if c in sq:
            return True
    # infinity patch: z'^2 = xi*(1 - 16 t^2 + 16 t^3)
    for t in range(p2):
        g = (1 - 16*t*t + 16*t*t*t) % p2
        c = (xi_img * g) % p2
        if c in sq:
            return True
    return False

# ---------- candidates: 8 classes passing N in Q*^2 ----------
# pi exponent must be 0 (N=-2); 37 exponent = a1+a2 even => {0,2}
# units: N=+1 among {1, e2, -e1, -e1*e2}
one = (1, 0, 0)
th3 = (3, 2, 0)            # N=37
p37_2 = (-41, -3, 7)       # N=-37
neg1 = (-1, 0, 0)
units_pos = [one, e2, mul(neg1, e1), mul(neg1, mul(e1, e2))]
print("\nunit reps (N should be +1):", [nrm(*u) for u in units_pos])

cands = [one]
for thp in [mul(th3, p37_2)]:   # 37-exponent 2 class
    for u in units_pos:
        cands.append(mul(thp, u))
print("\ncandidates (8 + 1):")
for c in cands:
    print("  ", c, "N =", nrm(*c))

# add -theta explicitly (class computed above)
all_cands = cands + [neg_theta]
print("\n=== local solubility (incl. -theta) ===")
selmer = []
seen = set()
for c in all_cands:
    # canonical: test square-equivalence later; just report local
    l1 = local_p37(c, 34, 17)   # p37_1: theta=34, pi=17
    l2 = local_p37(c, 20, 10)   # p37_2: theta=20, pi=10
    lp = local_p2(c)
    ok = l1 and l2 and lp
    print(f"xi={c} N={nrm(*c)}: p37_1={l1} p37_2={l2} p2={lp} -> {'SELMER' if ok else 'no'}")
    if ok:
        selmer.append(c)

print("\n|Sel^2| =", len(selmer))
for c in selmer:
    print("  ", c, "N =", nrm(*c))
print("expect: {1=(1,0,0), -theta=(0,-2,0)} -> dim 1 -> rank E(Q) <= 1")
