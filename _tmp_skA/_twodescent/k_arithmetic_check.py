# -*- coding: utf-8 -*-
"""Step 0: K = Q(theta), theta^3 - 16 theta + 16 = 0 — field arithmetic grounding.

Facts to pin down:
  f = x^3 - 16x + 16,  disc(f) = 9472 = 2^8 * 37  (>0 => totally real, r1=3, r2=0)
  Minkowski bound (r2=0): M = (6/27)*sqrt(|dK|)
  Dedekind criterion at p=2 and p=37: does p divide c = [O_K : Z[theta]]?
  dK = disc(f)/c^2.
"""
import sympy as sp

x = sp.symbols('x')
f = x**3 - 16*x + 16
Df = sp.discriminant(f, x)
print("disc(f) =", Df, "=", sp.factorint(Df))
print("totally real:", Df > 0, "| roots:", sp.nroots(f, n=30))

for p in [2, 37]:
    print(f"\n--- p = {p} ---")
    fac_terms = sp.factor_list(f, modulus=p)  # (unit, [(poly, exp), ...]) in GF(p)
    print("factor_list:", [(str(g), e) for g, e in fac_terms[1]])
    # factor_list returns (unit, [(poly, exp), ...]) with poly in GF(p)
    prod = sp.Integer(1)
    for g, e in fac_terms[1]:
        prod = prod * (g.as_expr() ** e)
    # lift to integer poly with reps in [0, p-1]
    from sympy import expand, together
    f_int = sp.Poly(f, x)
    prod_expr = expand(prod)
    num = sp.Poly(expand(f_int.as_expr() - prod_expr), x)
    h = sp.Poly((expand(f_int.as_expr() - prod_expr)) / p, x)  # may not be integral if error
    hcoeffs = [int(c) % p for c in h.all_coeffs()]
    hmod = sum(c * x**(len(hcoeffs)-1-i) for i, c in enumerate(hcoeffs))
    ok_all = True
    for g, e in fac_terms[1]:
        g = sp.Poly(g, x, modulus=p)
        if g.degree() == 1:
            # g = x - a  (a in GF(p)); root a
            a = int((-g.coeff_monomial(x**0)) % p)  # constant term negated, mod p
            hval = int(hmod.subs(x, a)) % p if hmod != 0 else 0
            print(f"  g=x-{a}: h({a}) mod p = {hval}  -> {'divides' if hval == 0 else 'p | c'}")
            if hval != 0:
                ok_all = False
        else:
            print(f"  g degree {g.degree()}: nonlinear, skip")
    print("  p divides conductor c =", not ok_all)

print("\n=> if p | c then p^2 | disc(f); disc(f) has 37 to the first power only.")
print("  Need to resolve which conclusion is right (check LMFDB 3.9472 / 3.2368 etc).")
