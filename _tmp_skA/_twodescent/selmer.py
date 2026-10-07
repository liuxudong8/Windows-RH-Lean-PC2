# -*- coding: utf-8 -*-
"""Step 4-6: Selmer 2-descent, E = 37a1 (E': Y^2 = X^3 - 16X + 16, no 2-torsion).

K = Q(theta), theta^3 - 16 theta + 16 = 0;  O_K = Z[pi], pi = theta/2,
pi^3 - 4 pi + 2 = 0.  dK = 148, h = 1, units rank 2.
S = {p2 (e=3,f=1), p37_1 (e=1,f=1, theta=34), p37_2 (e=2,f=1, theta=20)}.
K(S,2) basis (dim 5 => 32 cands):
  b0 = pi            (p2),        N = -2
  b1 = theta+3       (p37_1),     N = 37
  b2 = p37_2 rep     (norm +-37), N = +-37
  b3 = eps1 = -73 -5 pi +29 pi^2, N = -1
  b4 = eps2 = -71 +10 pi +19 pi^2, N = +1
Sel^2 = { xi in K(S,2) : N(xi) in Q*^2  and  C_xi(K_p) != empty for all p in S }
C_xi: z^2 = xi * f(x), f(x) = x^3 - 16x + 16  (K_v = K tensor Q_v).

Local solubility: for p in {2, 37} and each prime ideal above, enumerate
x in O_K / p^k (f=1 => Z/p^k), check z^2 == sigma_p(xi)*f(x) has a solution
mod p^k (k = 8 for p=2, k = 2 for p=37).  Sufficient by Hensel (regular), and
for degenerate points we use the full mod p^k square-set check.
"""
import sympy as sp
import mpmath as mp

# ---------- norm form on basis 1, pi, pi^2 ----------
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

# ---------- find p37_2 rep: N = +-37 and X + 10Y + 26Z = 0 (mod 37) ----------
p37_2 = None
for X in range(-60, 61):
    for Y in range(-60, 61):
        for Z in range(-60, 61):
            if (X + 10*Y + 26*Z) % 37 == 0:
                v = nrm(X, Y, Z)
                if abs(v) == 37:
                    p37_2 = (X, Y, Z, v)
                    break
        if p37_2: break
    if p37_2: break
print("p37_2 rep:", p37_2, "| N =", p37_2[3] if p37_2 else None)
if not p37_2:
    print("no p37_2 rep found with |coeff|<=60; will search wider")
    for X in range(-120, 121):
        for Y in range(-120, 121):
            for Z in range(-120, 121):
                if (X + 10*Y + 26*Z) % 37 == 0:
                    v = nrm(X, Y, Z)
                    if abs(v) == 37:
                        p37_2 = (X, Y, Z, v)
                        break
            if p37_2: break
        if p37_2: break
    print("wider search p37_2 rep:", p37_2)

# ---------- K(S,2) basis ----------
bases = {
    'pi':        (0, 1, 0),       # b0: pi, p2 class, N=-2
    'th3':       (3, 2, 0),       # b1: theta+3 = 3+2pi, p37_1, N=37
    'p37_2':     (p37_2[0], p37_2[1], p37_2[2]) if p37_2 else (0, 0, 0),
    'e1':        (-73, -5, 29),   # b3: unit, N=-1
    'e2':        (-71, 10, 19),   # b4: unit, N=+1
}
print("\nK(S,2) basis norms:", {k: nrm(*v) for k, v in bases.items()})

# ---------- candidates: 2^5 combos, filter N(xi) in Q*^2 ----------
names = list(bases.keys())
vecs = [bases[k] for k in names]

def mul(a, b):
    # (a0+a1 pi+a2 pi^2)*(b0+b1 pi+b2 pi^2) mod relation pi^3 = 4pi - 2
    A0, A1, A2 = a; B0, B1, B2 = b
    # polynomial product in t, then reduce t^3 = 4t - 2 (=> t^4 = 4t^2 - 2t)
    # c = a*b : t^0..t^4 coefficients
    c0 = A0*B0
    c1 = A0*B1 + A1*B0
    c2 = A0*B2 + A1*B1 + A2*B0
    c3 = A1*B2 + A2*B1
    c4 = A2*B2
    # t^3 -> 4t - 2 ; t^4 = t*t^3 -> 4t^2 - 2t
    r0 = c0 - 2*c3
    r1 = c1 + 4*c3 - 2*c4
    r2 = c2 + 4*c4
    return (r0, r1, r2)

def to_rat(v, pi):
    return v[0] + v[1]*pi + v[2]*pi**2

# rational check: N(xi) in Q*^2
def is_sq_rat(n):
    if n < 0:
        return False
    r = mp.sqrt(mp.mpf(n))
    return abs(r - mp.nint(r)) < mp.mpf('1e-40')

cands = []
for mask in range(32):
    acc = (1, 0, 0)
    sel = []
    for i in range(5):
        if mask >> i & 1:
            acc = mul(acc, vecs[i])
            sel.append(names[i])
    Nv = nrm(*acc)
    cands.append((mask, sel, acc, Nv, is_sq_rat(Nv)))
    print(f"cand {mask:02b}: {sel}  xi={acc}  N={Nv}  N in Q*^2={is_sq_rat(Nv)}")

# ---------- local solubility ----------
# prime ideal data: (name, p, root_theta mod p, k, pi image)
PRIMES = [
    # p37_1: theta = 34, pi = 17 ; k=2
    ('p37_1', 37, 34, 17, 2),
    # p37_2: theta = 20, pi = 10 ; k=2
    ('p37_2', 37, 20, 10, 2),
    # p2: theta = 0 mod 2, pi = uniformizer (pi^3 = 4pi - 2 mod 2^8); k=8
    ('p2', 2, None, None, 8),
]

def f_int(X):
    return X**3 - 16*X + 16

def local_soluble_full(xiv, p, theta_r, pi_r, k):
    """embedding: pi -> pi_r mod p^k ; x variable ranges Z/p^k (f=1)."""
    p2 = p**k
    sq = { (z*z) % p2 for z in range(p2) }
    X0, X1, X2 = xiv
    xi_img = (X0 + X1*pi_r + X2*(pi_r*pi_r % p2)) % p2
    for xx in range(p2):
        c = (xi_img * f_int(xx)) % p2
        if c in sq:
            return True
    return False
def ring_add(a, b):
    return ((a[0]+b[0]) % 2**8, (a[1]+b[1]) % 2**8, (a[2]+b[2]) % 2**8)

def ring_mul(a, b):
    A0, A1, A2 = a; B0, B1, B2 = b
    c0 = A0*B0; c1 = A0*B1 + A1*B0; c2 = A0*B2 + A1*B1 + A2*B0
    c3 = A1*B2 + A2*B1; c4 = A2*B2
    r0 = c0 - 2*c3
    r1 = c1 + 4*c3 - 2*c4
    r2 = c2 + 4*c4
    m = 2**8
    return (r0 % m, r1 % m, r2 % m)

def ring_sub(a, b):
    m = 2**8
    return ((a[0]-b[0]) % m, (a[1]-b[1]) % m, (a[2]-b[2]) % m)

def local_soluble_p2_full(xiv, k=8):
    m = 2**k
    # enumerate all ring elements as (a,b,c), a,b,c in Z/2^k — too many (2^24).
    # f=1, residue F2: ring has 2^k elements; enumerate pi-adic expansions.
    # Build all elements: start with {0}, multiply by pi repeatedly.
    # elements = { (a,b,c) } via linear combos of pi^i (i<k).
    elems = set()
    cur = (1 % m, 0, 0)
    one = (1 % m, 0, 0)
    pi = (0, 1 % m, 0)
    # pi^i for i in 0..k-1
    powers = [(1 % m, 0, 0)]
    for i in range(1, k):
        powers.append(ring_mul(powers[-1], pi))
    for bits in range(2**k):
        acc = (0, 0, 0)
        for i in range(k):
            if bits >> i & 1:
                acc = ring_add(acc, powers[i])
        elems.add(acc)
    # sanity: ring size should be 2^k
    assert len(elems) == 2**k, f"ring size {len(elems)} != 2^{k}"
    sq = { ring_mul(e, e) for e in elems }
    # xi as ring element
    X0, X1, X2 = xiv
    xi_el = (X0 % m, X1 % m, X2 % m)
    # f(x) = x^3 - 16x + 16 as ring element
    sixteen = (16 % m, 0, 0)
    for xx in elems:
        xx3 = ring_mul(ring_mul(xx, xx), xx)
        fval = ring_add(ring_sub(xx3, ring_mul(sixteen, xx)), sixteen)
        c = ring_mul(xi_el, fval)
        if c in sq:
            return True
    return False

# run local checks on candidates
print("\n=== local solubility ===")
selmer = []
for mask, sel, acc, Nv, okN in cands:
    if not okN:
        continue
    loc = []
    for (nm, p, thr, pir, k) in PRIMES:
        if p == 2:
            ok = local_soluble_p2_full(acc, k)
        else:
            ok = local_soluble_full(acc, p, thr, pir, k)
        loc.append((nm, ok))
    allok = all(o for _, o in loc)
    print(f"mask {mask:02b} {sel}: N ok, local: {loc} -> {'SELMER' if allok else 'no'}")
    if allok:
        selmer.append((mask, sel, acc))

print("\n=== Sel^2(E/Q) ===")
print("|Sel^2| =", len(selmer))
for m, s, a in selmer:
    print("  ", s, "xi =", a, "N =", nrm(*a))
print("\nexpect Sel^2 = {1, -theta = -2pi} (dim 1), theta = 2pi")
print("1     = coeff (1,0,0)")
print("-theta = coeff (0,-2,0)")
