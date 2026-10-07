# -*- coding: utf-8 -*-
"""Debug selmer local check at p2 for e2 = (-71,10,19)."""
m = 2**8

def ring_mul(a, b):
    A0, A1, A2 = a; B0, B1, B2 = b
    c0 = A0*B0; c1 = A0*B1 + A1*B0; c2 = A0*B2 + A1*B1 + A2*B0
    c3 = A1*B2 + A2*B1; c4 = A2*B2
    r0 = c0 - 2*c3
    r1 = c1 + 4*c3 - 2*c4
    r2 = c2 + 4*c4
    return (r0 % m, r1 % m, r2 % m)

def ring_add(a, b):
    return ((a[0]+b[0]) % m, (a[1]+b[1]) % m, (a[2]+b[2]) % m)

def ring_sub(a, b):
    return ((a[0]-b[0]) % m, (a[1]-b[1]) % m, (a[2]-b[2]) % m)

one = (1 % m, 0, 0)
pi = (0, 1 % m, 0)
powers = [(1 % m, 0, 0)]
for i in range(1, 8):
    powers.append(ring_mul(powers[-1], pi))

elems = set()
for bits in range(2**8):
    acc = (0, 0, 0)
    for i in range(8):
        if bits >> i & 1:
            acc = ring_add(acc, powers[i])
    elems.add(acc)
assert len(elems) == 2**8

sq = { ring_mul(e, e) for e in elems }
print("pi^3 =", powers[3], " (expect -2,4,0)")
print("pi^2 =", powers[2])
print("pi^4 =", powers[4])

def f_int(X):  # in ring: x^3 - 16x + 16
    sixteen = (16 % m, 0, 0)
    xx3 = ring_mul(ring_mul(X, X), X)
    return ring_add(ring_sub(xx3, ring_mul(sixteen, X)), sixteen)

xi = (-71 % m, 10, 19)
print("xi =", xi)

hits = []
for xx in sorted(elems):
    c = ring_mul(xi, f_int(xx))
    if c in sq:
        hits.append((xx, f_int(xx), c))
        if len(hits) <= 5:
            pass
print("num x hits:", len(hits))
if hits:
    for h in hits[:10]:
        print("  x=", h[0], "f=", h[1], "c=", h[2])

# also check without xi (xi=1)
hits1 = []
for xx in sorted(elems):
    c = f_int(xx)
    if c in sq:
        hits1.append((xx, c))
print("num x hits (xi=1):", len(hits1))
for h in hits1[:10]:
    print("  x=", h[0], "f=", h[1])
