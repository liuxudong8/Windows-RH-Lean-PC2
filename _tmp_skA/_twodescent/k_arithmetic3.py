# -*- coding: utf-8 -*-
"""Step 1-3 (corrected): K = Q(theta), theta^3-16 theta+16 = 0.

CERTAIN FACTS:
  pi = theta/2 is a uniformizer at 2;  h(T) = T^3 - 4T + 2 is 2-Eisenstein
  with v2(a0)=1  =>  Z[pi] = O_K  (integral basis 1, pi, pi^2).
  disc(h) = 148  =>  dK = 148,  conductor c = [O_K : Z[theta]] = 8.
  N(pi) = -2 => p2 = (pi) principal => class group trivial (Minkowski 2.70, only p2).
  2 totally ramified: 2 O_K = p2^3;  37: (x+3)(x+17)^2 => p37_1 (e1 f1), p37_2 (e2 f1).

Norm form on basis 1, pi, pi^2  (pi^3 = 4 pi - 2):
  M = [[x, -2z, -2y], [y, x+4z, 4y-2z], [z, y, x+4z]]
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 50
x, y, z = sp.symbols('x y z')
M = sp.Matrix([
    [x, -2*z, -2*y],
    [y, x + 4*z, 4*y - 2*z],
    [z, y, x + 4*z],
])
Nm = sp.expand(M.det())
print("norm(x + y*pi + z*pi^2) =", sp.factor(Nm))

# fast integer evaluation: extract coefficients of the cubic form
poly = sp.Poly(Nm, x, y, z)
coefs = {}
for mon, coef in poly.terms():
    coefs[tuple(mon)] = int(coef)  # (dx, dy, dz)

def nrm(X, Y, Z):
    return sum(c * X**dx * Y**dy * Z**dz for (dx, dy, dz), c in coefs.items())

# --- class group: p2 = (pi) principal, N(pi) = -2 ---
print("\n=== class group ===")
print("N(pi) = -2, p2 = (pi) principal -> h(K) = 1 (Minkowski 2.70, only prime ideal p2)")
print("Minkowski =", mp.mpf(6)/27*mp.sqrt(148))

# --- units: N = +-1 ---
print("\n=== units (rank 2) ===")
units = []
for X in range(-80, 81):
    for Y in range(-80, 81):
        for Z in range(-80, 81):
            v = nrm(X, Y, Z)
            if abs(v) == 1:
                units.append((X, Y, Z, v))
print("N=+-1 solutions (|c|<=80):", units[:40], "count:", len(units))
# reduce to independent generators mod +/-1: take pairs with independent log-embedding
def embed(wx, wy, wz):
    # sigma_i(pi) = theta_i / 2
    th = [mp.mpf('-4.4286394867550703748309954017022277348031120402793'),
          mp.mpf('1.0783777456217782330517518054031590409595519412372'),
          mp.mpf('3.3502617411332921417792435962980686938435600990425')]
    return [wx + wy*t/2 + wz*(t/2)**2 for t in th]
if units:
    basis = []
    from itertools import combinations
    for (X1,Y1,Z1,_),(X2,Y2,Z2,_) in combinations(units[:20], 2):
        l1 = [mp.log(abs(s)) for s in embed(X1,Y1,Z1)]
        l2 = [mp.log(abs(s)) for s in embed(X2,Y2,Z2)]
        det = l1[0]*l2[1]-l1[1]*l2[0]
        if abs(det) > mp.mpf('1e-20'):
            basis = [(X1,Y1,Z1),(X2,Y2,Z2)]
            print("independent unit pair:", basis, "|log-det| =", abs(det))
            break
    if not basis:
        print("no independent pair found in first 20; need larger search")

# --- p37_2 generator: N = +-37 ---
print("\n=== p37_1, p37_2 ===")
print("N(theta+3) =", int(sp.N((sp.symbols('t')**3 - 16*sp.symbols('t') + 16).subs(sp.symbols('t'), -3))),
      "-> (theta+3) = p37_1")
print("theta+3 in pi-basis: theta = 2pi -> 2pi+3 =", "3 + 2*pi  -> coeff (3, 2, 0)")
sols37 = []
for X in range(-60, 61):
    for Y in range(-60, 61):
        for Z in range(-60, 61):
            v = nrm(X, Y, Z)
            if abs(v) == 37:
                sols37.append((X, Y, Z, v))
print("N = +-37 solutions (|c|<=60):", sols37[:20], "count:", len(sols37))

# --- delta(P0) = -theta = -2pi ---
print("\n=== delta(P0) ===")
print("-theta = -2pi  (coeff (0,-2,0));  N(-theta) =", nrm(0, -2, 0),
      "= 16 = 4^2 in Q*^2  -> in K(S,2), support {p2} only")
