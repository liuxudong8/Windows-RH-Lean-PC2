# -*- coding: utf-8 -*-
"""Determine class of -theta = (0,-2,0) among signed basic-unit classes, high precision.
Square test for element w: all embeddings > 0 and log(w)/2 in unit log lattice.
"""
import mpmath as mp
mp.mp.dps = 80

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

eta1 = (-15, -48, 34)   # N=+1
eta2 = (-9, -3, 5)      # N=-1
neg_theta = (0, -2, 0)

le1 = [mp.log(mp.fabs(t)) for t in conj(eta1)]
le2 = [mp.log(mp.fabs(t)) for t in conj(eta2)]
G = mp.matrix([[le1[0], le2[0]], [le1[1], le2[1]]])

def is_square(w):
    wc = conj(w)
    if any(t.real <= mp.mpf('1e-30') for t in wc):
        return False, None
    lw = [mp.log(t) for t in wc]
    b = mp.matrix([lw[0], lw[1]])
    c = mp.lu_solve(G, b)   # coords of log(w)/2? no: solve log(w) = c1*le1 + c2*le2
    # want log(w)/2 in lattice: (c1/2, c2/2) integers
    c2h = (c[0]/2, c[1]/2)
    r = max(abs(c2h[0] - mp.nint(c2h[0])), abs(c2h[1] - mp.nint(c2h[1])))
    return r < mp.mpf('1e-20'), (c[0], c[1], r)

one = (1, 0, 0); neg1 = (-1, 0, 0)
classes = {}
for a in (0, 1):
    for b in (0, 1):
        for s in (1, -1):
            acc = one
            if a: acc = mul(acc, eta1)
            if b: acc = mul(acc, eta2)
            if s == -1: acc = mul(acc, neg1)
            # test: is (neg_theta * acc) square?  (acc^2 = 1 in K*/K*^2)
            w = mul(neg_theta, acc)
            ok, info = is_square(w)
            print(f"class (a={a},b={b},s={s:+d}) rep={acc}: -theta*rep square? {ok}", "" if not info else f"coords={mp.nstr(info[0],6)},{mp.nstr(info[1],6)} r={mp.nstr(info[2],4)}")
            if ok:
                classes[(a, b, s)] = acc

print("\n- theta class found:", classes)

# cross-check: is (9,3,-5) == -eta2?  (-eta2 = mul(neg1, eta2))
m9 = mul(neg1, eta2)
print("(-1)*eta2 =", m9)
w2 = mul(neg_theta, m9)
ok2, info2 = is_square(w2)
print("-theta * (-eta2) square?", ok2, info2)
