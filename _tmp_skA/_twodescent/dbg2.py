# -*- coding: utf-8 -*-
"""Debug: same xi=(-151,-35,15) local_p2 in selmer2 vs selmer3."""
m = 2**8

def ring_mul8(a, b):
    A0, A1, A2 = a; B0, B1, B2 = b
    c0 = A0*B0; c1 = A0*B1 + A1*B0; c2 = A0*B2 + A1*B1 + A2*B0
    c3 = A1*B2 + A2*B1; c4 = A2*B2
    return ((c0 - 2*c3) % m, (c1 + 4*c3 - 2*c4) % m, (c2 + 4*c4) % m)

def ring_add8(a, b):
    return ((a[0]+b[0]) % m, (a[1]+b[1]) % m, (a[2]+b[2]) % m)

def ring_sub8(a, b):
    return ((a[0]-b[0]) % m, (a[1]+b[1]) % m, (a[2]+b[2]) % m)

def ring_elems8():
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

xi = (-151 % m, -35 % m, 15 % m)
sixteen = (16 % m, 0, 0)
def fval(X):
    xx3 = ring_mul8(ring_mul8(X, X), X)
    return ring_add8(ring_sub8(xx3, ring_mul8(sixteen, X)), sixteen)

elems = ring_elems8()
sq = { ring_mul8(e, e) for e in elems }
powers = [(1, 0, 0)]
pi = (0, 1, 0)
for i in range(1, 8):
    powers.append(ring_mul8(powers[-1], pi))

print("xi mod 256:", xi)
print("== w patches (x = pi^w * e) ==")
for w in (0, 2, 4, 6):
    pw = powers[w]
    n_hit = 0
    ex = None
    for e in elems:
        c = ring_mul8(xi, fval(ring_mul8(pw, e)))
        if c in sq:
            n_hit += 1
            if ex is None:
                ex = (e, c)
    print(f"w={w}: hits={n_hit}", ("first hit x0=%s c=%s" % (ex[0], ex[1])) if ex else "")

print("== infinity patch (t) ==")
n_hit = 0
ex = None
for t in elems:
    t2 = ring_mul8(t, t); t3 = ring_mul8(t2, t)
    g = ring_add8(ring_sub8((1 % m, 0, 0), ring_mul8(sixteen, t2)), ring_mul8(sixteen, t3))
    c = ring_mul8(xi, g)
    if c in sq:
        n_hit += 1
        if ex is None:
            ex = (t, c)
print(f"t-patch: hits={n_hit}", ("first hit t=%s c=%s" % (ex[0], ex[1])) if ex else "")

# also w odd patches (valuation of xi at p2 = ?): N(xi)=1369, xi has no pi factor
# check v_p2(xi)
def v_p2(cv):
    X0, X1, X2 = cv
    # valuation via pi-adic: reduce
    v = 0
    cur = (X0 % m, X1 % m, X2 % m)
    while cur != (0, 0, 0) and v < 8:
        # is cur divisible by pi? cur = pi * q  <=>  cur == ring_mul8((0,1,0), q)
        found = False
        for q in elems:
            if ring_mul8((0, 1, 0), q) == cur:
                found = True
                cur = q
                break
        if not found:
            break
        v += 1
    return v

print("v_p2(xi) =", v_p2(xi))
