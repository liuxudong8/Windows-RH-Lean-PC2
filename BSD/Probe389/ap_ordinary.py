# -*- coding: utf-8 -*-
# 389a1 正确最小模型: [a1,a2,a3,a4,a6] = [0,1,1,-2,0]
#   y^2 + y = x^3 + x^2 - 2x   (注意: 之前误用 y^2+y=x^3-x^2-2x+1)
# a_p = p + 1 - N_p ;  ordinary at p (good reduction)  ⟺  a_p != 0 (mod p)

def count_points(p):
    n = 1  # 无穷远点
    for x in range(p):
        rhs = (x**3 + x**2 - 2*x) % p
        cnt = sum(1 for y in range(p) if (y*y + y) % p == rhs)
        n += cnt
    return n

primes = [2, 3, 5, 7, 11, 13, 17, 19]
print("p   N_p   a_p   a_p mod p   ordinary?")
for p in primes:
    N = count_points(p)
    a = p + 1 - N
    ord_ = "YES" if a % p != 0 else "NO (p=2 恒非ordinary / supersingular)"
    print(f"{p:2d}  {N:4d}  {a:4d}   {a % p:3d}        {ord_}")
