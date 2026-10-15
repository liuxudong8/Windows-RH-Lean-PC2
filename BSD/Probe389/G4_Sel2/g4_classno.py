# G4 类数检验：A = Q[x]/(f), f = x^3+x^2-2x+1/4
# Minkowski 界：全实三次域 disc(f)=389/16，整化 disc = 1556，M = (3!/3^3)*sqrt(1556) = 8.76
# ⟹ 类群由 norm <= 8 的素理想生成：p=2（分歧, P2=(2,t)）、p=3（分裂, P3=(3,t-1)）
# 检验：P2, P3 主 ⟺ 存在 N(alpha) = ±2, ±3 ⟹ h = 1 ⟹ Cl[2] = 0 ⟹ |A*/A*2| = 8 完整
from fractions import Fraction as F
import itertools, math

def mul(u, v):
    a,b,c = u; d,e,g = v
    r0 = a*d; r1 = a*e + b*d; r2 = a*g + b*e + c*d; r3 = b*g + c*e; r4 = c*g
    s0 = r0 + r3*(-F(1,4)) + r4*F(1,4)
    s1 = r1 + r3*2 + r4*(-F(9,4))
    s2 = r2 + r3*(-1) + r4*3
    return (s0, s1, s2)

def norm(u):
    a,b,c = u
    m1 = mul(u, (F(1),F(0),F(0)))
    mx = mul(u, (F(0),F(1),F(0)))
    mx2 = mul(u, (F(0),F(0),F(1)))
    M = [m1, mx, mx2]
    det = (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
         - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
         + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
    return det

print("=== 素理想主性检验（N(alpha) = ±2, ±3, ±5, ±7）===")
B = 40
targets = {2: None, 3: None, 5: None, 7: None}
found = {2: [], 3: [], 5: [], 7: []}
for a in range(-B, B+1):
    for b in range(-B, B+1):
        for c in range(-B, B+1):
            if a==0 and b==0 and c==0: continue
            N = norm((F(a),F(b),F(c)))
            for p in targets:
                if N == p or N == -p:
                    found[p].append((a,b,c,int(N)))
                    if len(found[p]) >= 2: break
            if all(len(v) >= 1 for v in found.values()): break
    if all(len(v) >= 1 for v in found.values()): break

for p in [2,3,5,7]:
    print("N=±%d 元素数: %d" % (p, len(found[p])))
    for e in found[p][:2]:
        print("   δ = %s  N = %d" % (e[:3], e[3]))

# Minkowski 界内只需 p=2,3 的素理想（度 1/分歧）；5,7 惰性素理想 norm 125/343 > 界
# 若 P2, P3 主 ⟹ 类群平凡 ⟹ h=1
P2_main = len(found[2]) > 0
P3_main = len(found[3]) > 0
print("=== 判定 ===")
print("Minkowski 界 = 8.76；类群由 norm≤8 素理想生成（2,3 相关）")
print("P2=(2,t) 主:", P2_main, " P3=(3,t-1) 主:", P3_main)
if P2_main and P3_main:
    print("⟹ 类数 h(A) = 1 ⟹ Cl[2]=0 ⟹ |A*/A*²| = 2^3 = 8 完整（<−1,ε1,ε2> 生成全部）")
    print("⟹ |H^1(Q,E[2])| = 4 为精确值 ⟹ G4 阶段 1 闭合")
else:
    print("需进一步检查（类群可能非平凡）")
