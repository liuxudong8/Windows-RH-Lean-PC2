# -*- coding: utf-8 -*-
"""Find TRUE basic unit pair: include u' = (15,-2,-4) and all units |c|<=80."""
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

th1 = mp.findroot(lambda t: t**3 - 16*t + 16, 3.35)
th2 = mp.findroot(lambda t: t**3 - 16*t + 16, 1.08)
th3 = mp.findroot(lambda t: t**3 - 16*t + 16, -4.43)
ths = [th1, th2, th3]
pis = [t/2 for t in ths]
def conj(cvec):
    X0, X1, X2 = cvec
    return [X0 + X1*p + X2*p*p for p in pis]

# units |c|<=80 plus u'=(15,-2,-4)
units_c = {(15, -2, -4)}
for X in range(-80, 81):
    for Y in range(-80, 81):
        for Z in range(-80, 81):
            if abs(nrm(X, Y, Z)) == 1:
                units_c.add((X, Y, Z))
print("unit count:", len(units_c))

def log2(cvec):
    return [mp.log(mp.fabs(t)) for t in conj(cvec)]

best = []
for a, b in itertools.combinations(units_c, 2):
    la = log2(a); lb = log2(b)
    d = la[0]*lb[1] - la[1]*lb[0]
    if mp.fabs(d) > mp.mpf('1e-8'):
        ad = mp.fabs(d)
        best.append((ad, a, b))
best.sort(key=lambda t: t[0])
print("top 6 smallest |log-det| pairs:")
for ad, a, b in best[:6]:
    print(f"  det={mp.nstr(ad,8)}  {a} N={nrm(*a)}  |  {b} N={nrm(*b)}")
