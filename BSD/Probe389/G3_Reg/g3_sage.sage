# G3：389a1 Reg 全精度比对（Sage）
E = EllipticCurve('389a1')
print("model:", E)
print("gens:", E.gens())
try:
    r = E.regulator()
    print("E.regulator() =", r)
    print("digits:", r.n(digits=30))
except Exception as e:
    print("regulator err:", e)
try:
    P, Q = E.gens()
    H = E.height_pairing_matrix([P, Q])
    print("height_pairing_matrix =")
    print(H)
    print("det =", H.determinant())
except Exception as e:
    print("hpm err:", e)
print("LMFDB target 0.152460177943")
# 额外：精确位数核对
from sage.all import RealField
R = RealField(200)
try:
    reg = E.regulator(precision=200)
    print("regulator(p=200) =", reg)
except Exception as e:
    print("high prec err:", e)
