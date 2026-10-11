# calib43_eside.py - LSeries5_43 数值准备 (2026-10-11)
# E = 43a1 (y^2+y=x^3+x^2), E^5 = E x chi_5, alpha = 2*pi/sqrt(1075)
import math
GAMMA = 0.57721566490153286060651209008240243104215933593992

# --- aE5 前 50 项（读 aE5_raw_43 表：43->1 特判已修） ---
aE5 = {}
with open(r"C:\proj2\BSD\aE5_table_43.lean") as f:
    for line in f:
        line = line.strip()
        if line.startswith("|") and "=>" in line:
            try:
                n, v = line[1:].split("=>")
                aE5[int(n.strip())] = int(v.strip())
            except Exception:
                pass

alpha = 2 * math.pi / math.sqrt(1075)
print("alpha =", repr(alpha))
print("exp(-alpha) =", repr(math.exp(-alpha)))
print("sqrt1075 =", repr(math.sqrt(1075)))

# 幂底：qneg=0.8254 (下界, 正项), qpos=0.8258 (上界, 负项)
qneg, qpos = 0.8254, 0.8258
print("qneg^50 =", repr(qneg**50), " qpos^51 =", repr(qpos**51))

# crude 部分和（模拟 term_i 底选择：正项用 qneg, 负项用 qpos, 零项跳过）
crude = 0.0
sign_info = []
for n in range(1, 51):
    a = aE5.get(n, 0)
    if a > 0:
        crude += a / n * qneg**n
        sign_info.append((n, a, 'N'))
    elif a < 0:
        crude += a / n * qpos**n
        sign_info.append((n, a, 'P'))
    else:
        sign_info.append((n, a, '0'))
print("crude sum (R) =", repr(crude))
print("crude - 2.3 =", repr(crude - 2.3))

# 部分和精确值（用真 exp(-alpha(n+1)) 与表值）
S = 0.0
for n in range(1, 51):
    S += aE5.get(n, 0) / n * math.exp(-alpha * n)
print("exact partial sum S_50 =", repr(S), " L/2 ~", repr(S + 0.0003))

# 尾界 B = 2*e^(-alpha*51)/(1-e^(-alpha))
B = 2 * math.exp(-alpha * 51) / (1 - math.exp(-alpha))
print("tail B =", repr(B), " 2B =", repr(2 * B))
print("2*2.3 - 2B =", repr(4.6 - 2 * B))

# E1(alpha) 参考（L(E^5,1) 部分）
def E1(x):
    if x <= 25:
        s = 0.0; term = 1.0; k = 1
        while True:
            term *= -x / k; t = term / k; s += t; k += 1
            if k > 400 or abs(t) < 1e-20 * (1 + abs(s)): break
        return -GAMMA - math.log(x) - s
    s = 1.0; f = 1.0; sign = -1.0; k = 1; xinv = 1.0 / x; prev = 0.0
    while True:
        f *= k; t = sign * f * (xinv ** (k + 1))
        if k > 1 and abs(t) > abs(prev): break
        s += t; prev = t; sign = -sign; k += 1
        if k > 200: break
    return math.exp(-x) * s / x

# L(E^5,1) = 2 * sum_{n>=1} aE5(n)/n * E1(alpha*n)（部分和 800）
L = 0.0
for n in range(1, 801):
    a = aE5.get(n, 0)
    if a != 0:
        L += 2 * a / n * E1(alpha * n)
print("L(E^5,1) partial 800 =", repr(L))

# 分块界（native_decide ℚ 用）：crude 分成 5 块×10 项
for b in range(5):
    s = 0.0
    for n in range(10 * b + 1, 10 * b + 11):
        a = aE5.get(n, 0)
        q = qneg if a >= 0 else qpos
        s += a / n * q**n
    print(f"block {b} (n={10*b+1}..{10*b+10}): {s!r}")
