# -*- coding: utf-8 -*-
"""
λ⁺(r) 求值 (复共轭/star involution 版) — N=11 校准.
================================================================
正确路线 (Sage ell_modular_symbols.py verbatim):
  sign=±1 空间 = 复共轭 (star involution, z -> -z̄) 的 ±1 特征空间.
  λ⁺(r)Ω⁺ + λ⁻(r)Ω⁻ = ∫_∞^r 2πi f(z) dz.
关键公式:
  Cremona 2.3.2:  {0, α} = Σ_{j=1}^k (-1)^{j-1} (q_j : q_{j-1}), q = 收敛分母.
  Cremona 2.1.7:  {α, β} = {0, β} − {0, α}.
  σ 作用:  (c:d) = {b/d, a/c} (ad−bc=1)  ->  {−b/d, −a/c}.
锚 (Sage verbatim, 11a1 eclib):
  [Mplus(1/i) for i in 1..11]  = [1/5, −4/5, −3/10, 7/10, 6/5, 6/5, 7/10, −3/10, −4/5, 1/5, 0]
  [Mminus(1/i) for i in 1..11] = [0, 0, 1/2, 1/2, 0, 0, −1/2, −1/2, 0, 0, 0]
  (i=1 -> r=0, i=2..11 -> r=1/i, 因为 Sage __call__ 先做 numer % denom / denom)
"""
import math
from fractions import Fraction as F

def modinv(a, m):
    return pow(a % m, m - 2, m)

def egcd(a, b):
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = egcd(b, a % b)
    return (g, y1, x1 - (a // b) * y1)

# ---------- 1. M-symbol 空间 ----------

def build_space(Nv, include_boundary=True):
    """M-symbol 空间: 2-term 去重 + 3-term (+ 边界两行可选).
    include_boundary=True:  核 (ker δ, 2g 维, N=11 -> 2 维)   —— 找特征向量用
    include_boundary=False: M 的关系商 (3 维, N=11)            —— λ 求值配对用
    """
    gens = [(c, 1) for c in range(Nv)] + [(1, 0)]
    idx = {g: i for i, g in enumerate(gens)}
    n = len(gens)
    def nm(c, d):
        return idx[norm(c, d, Nv)]
    rows = []
    seen = set()
    for i, (c, d) in enumerate(gens):
        if i in seen:
            continue
        j = nm(-d, c)
        if j != i:
            row = [F(0)] * n
            row[i] = F(1); row[j] = F(1)
            rows.append(row); seen.add(i); seen.add(j)
        else:
            row = [F(0)] * n
            row[i] = F(1)
            rows.append(row); seen.add(i)
    for i, (c, d) in enumerate(gens):
        t1 = nm(c + d, -c); t2 = nm(d, -c - d)
        row = [F(0)] * n
        row[i] = F(1); row[t1] = F(1); row[t2] = F(1)
        rows.append(row)
    if include_boundary:
        # 真 δ 类坐标: δ(c:d) = [a/c]−[b/d]; 尖点类由分母模 N 决定
        # (分母 ≡ 0 mod N → ∞ 类; 否则 [0] 类). 对 (c:1)= {0,1/c}: [1/c]=[0] 类 ⟹ δ=0.
        # 行∞(i) = [N|c] − [N|d]:  (0:1)=1, (1:0)=−1, (c:1)=0.
        def delta_class(i):
            c, d = gens[i]
            return (1 if c % Nv == 0 else 0) - (1 if d % Nv == 0 else 0)
        row_inf = [F(delta_class(i)) for i in range(n)]
        rows.append(row_inf)
        rows.append([-x for x in row_inf])   # 行0 = −行∞ (δ 像 1 维, rank 1)
    return gens, idx, rows

def kernel_basis(rows_echelon, ncols):
    pivots = []
    for row in rows_echelon:
        for c in range(ncols):
            if row[c] != 0:
                pivots.append(c); break
    free = [c for c in range(ncols) if c not in set(pivots)]
    basis = []
    for fv in free:
        v = [F(0)] * ncols
        v[fv] = F(1)
        for row in rows_echelon:
            p = None
            for c in range(ncols):
                if row[c] != 0:
                    p = c; break
            if p in free:
                continue
            s = sum(row[j] * v[j] for j in range(ncols))
            v[p] = -s / row[p]
        basis.append(v)
    return basis, free

def gaussian(A):
    rows = [[F(x) for x in row] for row in A]
    m = len(rows); n = len(rows[0])
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if rows[i][c] != 0:
                piv = i; break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == m:
            break
    return rows[:r]

def matmul(A, B):
    n = len(A); m = len(B[0]); p = len(B)
    return [[sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)] for i in range(n)]

def matvec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]

def norm(c, d, Nv):
    c %= Nv; d %= Nv
    if d == 0:
        return (1, 0)
    return (c * modinv(d, Nv) % Nv, 1)

def reduce_v(v, ech):
    """向量 v 模关系约化到自由变量坐标 (RREF 行阶梯, 从后往前消主元)."""
    w = list(v)
    for row in reversed(ech):
        p = None
        for c in range(len(w)):
            if row[c] != 0:
                p = c; break
        if p is None:
            continue
        if w[p] != 0:
            f = w[p]
            w = [a - f * b for a, b in zip(w, row)]
    return w

# ---------- 2. 通用路径展开 {0, α} (Cremona 2.3.2) ----------

def expand0(r, reps, Nv):
    """{0, α} 的链 (reps 坐标): ⌊α⌋·(1:1) + Σ_{j≥1} (−1)^{j−1}(q_j:q_{j−1}).
    r = None 表示 ∞:  {0, ∞} = (0:1).
    """
    n = len(reps)
    idx = {g: i for i, g in enumerate(reps)}
    coords = [F(0)] * n
    if r is None:
        coords[idx[norm(0, 1, Nv)]] += F(1)
        return coords
    fl = r.numerator // r.denominator      # floor (Python // 对负向下取整)
    if fl != 0:
        coords[idx[norm(1, 1, Nv)]] += F(fl)
    rp = r - fl                             # ∈ [0,1)
    if rp == 0:
        return coords
    u, v = rp.numerator, rp.denominator
    terms = []
    while v != 0:
        qk = u // v
        terms.append(qk)
        u, v = v, u - qk * v
    # terms = [0, a1, a2, ...]; q_{-1}=0, q_0=1
    q_jm2, q_jm1 = F(0), F(1)
    sign = 1
    for j in range(1, len(terms)):
        ai = terms[j]
        qj = ai * q_jm1 + q_jm2
        coords[idx[norm(int(qj), int(q_jm1), Nv)]] += F(sign)
        sign = -sign
        q_jm2, q_jm1 = q_jm1, qj
    return coords

def expand_path(x, y, reps, Nv):
    """{x, y} = {0, y} − {0, x}.  x/y 为 Fraction 或 None(∞)."""
    cy = expand0(y, reps, Nv)
    cx = expand0(x, reps, Nv)
    return [cy[i] - cx[i] for i in range(len(reps))]

# ---------- 3. 复共轭 σ (star involution) ----------

def lift_ab(c, d):
    """求 (a,b) 使 a·d − b·c = 1 (扩展欧几里得)."""
    g, x, y = egcd(d, c)
    assert g == 1, (c, d, g)
    return x, -y

def sigma_matrix(reps, Nv):
    """σ (star involution): 由复共轭 z ↦ −z̄ 诱导, Cremona §2.4 Implementation:
    ∗ acts via (c : d) ↦ (−c : d).  数学上 = 路径反射 {b/d,a/c} -> {−b/d,−a/c},
    但置换实现自动保持 2-term/3-term 关系与边界, 是正确形式.
    列 i = 生成元 i 的像 (与 hecke_matrix 相同存储: M[k][i]).
    """
    n = len(reps)
    idx = {g: i for i, g in enumerate(reps)}
    M = [[F(0)] * n for _ in range(n)]
    for i, (c, d) in enumerate(reps):
        nc = (-c) % Nv
        if d % Nv == 0:
            rep = (1, 0)
        else:
            rep = (nc * modinv(d, Nv) % Nv, 1)
        j = idx[rep]
        M[j][i] = F(1)
    return M

# ---------- 4. Hecke (验证过, 保留) ----------

def roundf(x):
    return int(math.copysign(math.floor(abs(x) + 0.5), x))

def heilbronn_cremona(p):
    if p == 2:
        return [[1, 0, 0, 2], [2, 0, 0, 1], [2, 1, 0, 1], [1, 0, 1, 2]]
    L = [[1, 0, 0, p]]
    for r in range(-(p // 2), p // 2 + 1):
        x1, x2, y1, y2 = p, -r, 0, 1
        a, b = -p, r
        L.append([x1, x2, y1, y2])
        while b:
            q = roundf(a / b)
            c = a - b * q
            a, b = -b, c
            x3 = q * x2 - x1
            x1, x2 = x2, x3
            y3 = q * y2 - y1
            y1, y2 = y2, y3
            L.append([x1, x2, y1, y2])
    return L

def hecke_matrix(p, reps, Nv):
    n = len(reps)
    idx = {g: i for i, g in enumerate(reps)}
    M = [[F(0)] * n for _ in range(n)]
    for i, (c, d) in enumerate(reps):
        col = [F(0)] * n
        for h in heilbronn_cremona(p):
            a, b, cc, dd = h
            u = c * a + d * cc
            v = c * b + d * dd
            col[idx[norm(u, v, Nv)]] += F(1)
        for k in range(n):
            M[k][i] = col[k]
    return M

# ---------- 5. 求值管道 ----------

def restrict_to(Tp, ker):
    """算子 Tp (n×n) 限制到核基 {ker} (d 个 n 维向量) 上的 d×d 矩阵 (类坐标)."""
    d = len(ker)
    m = len(ker[0])
    kerT = [[ker[i][j] for i in range(d)] for j in range(m)]
    G = matmul(ker, kerT)
    aug = [[F(0)] * (2 * d) for _ in range(d)]
    for i in range(d):
        for j in range(d):
            aug[i][j] = G[i][j]
        aug[i][d + i] = F(1)
    echg = gaussian(aug)
    Ginv = [[echg[i][d + j] for j in range(d)] for i in range(d)]
    return matmul(Ginv, matmul(ker, matmul(Tp, kerT)))

def class_coords(v, ech, free):
    """向量 v (n 维) 在商基 (free) 下的类坐标."""
    rw = reduce_v(v, ech)
    return [rw[f] for f in free]

def lambda_raw(v, r, reps, Nv, ech3, free3):
    """λ(r) = v₃ · w₃ (3 维商基点积), v₃ = 约化(v), w₃ = 约化({∞,r}).
    注意: 配对在 M 的关系商 (无边界) 上进行, 与 Sage ambient 求值一致.
    """
    w = expand_path(None, r, reps, Nv)     # {∞, r}
    v3 = class_coords(v, ech3, free3)
    w3 = class_coords(w, ech3, free3)
    return sum(v3[i] * w3[i] for i in range(len(free3)))

# ---------- 6. 主流程 (N=11 校准) ----------

def run(Nv, A_P, anchors_plus, anchors_minus):
    # 核空间 (含边界) — 找 σ 特征向量
    reps, idx, rel_rows = build_space(Nv, include_boundary=True)
    n = len(reps)
    ech = gaussian(rel_rows)
    ker, free = kernel_basis(ech, n)
    d = len(ker)
    # 关系商 (无边界) — λ 求值配对
    reps3, idx3, rel_rows3 = build_space(Nv, include_boundary=False)
    ech3 = gaussian(rel_rows3)
    _, free3 = kernel_basis(ech3, n)
    d3 = len(free3)
    print("N=%d: reps %d, ker dim %d (Hecke 特征空间), 关系商 dim %d" % (Nv, n, d, d3))

    # Hecke 限制 + 公共核
    T = {p: restrict_to(hecke_matrix(p, reps, Nv), ker) for p in A_P}
    for p in A_P:
        print("  T%d|H:" % p, T[p])
    rows = []
    for p, a in A_P.items():
        M = [[T[p][i][j] - (F(a) if i == j else F(0)) for j in range(d)] for i in range(d)]
        rows.extend(M)
    ck, _ = kernel_basis(gaussian(rows), d)
    dk = len(ck)
    print("  common kernel dim:", dk)
    ckT = [[ck[i][j] for i in range(dk)] for j in range(d)]   # d×dk

    # σ 在核类坐标: σ·B_j ∈ 核 (置换保关系+边界) ⟹ 类坐标 = free 分量直接读
    S = sigma_matrix(reps, Nv)
    Sk = [[matvec(S, ker[j])[f] for f in free] for j in range(d)]   # 转置: Sk[i][j] = 坐标 i 分量 of σ·B_j
    Sk = [[Sk[j][i] for j in range(d)] for i in range(d)]           # 规范: Sk[i][j]
    Sk2 = matmul(Sk, Sk)
    id_ok = all(Sk2[i][j] == (F(1) if i == j else F(0)) for i in range(d) for j in range(d))
    print("  σ on ker (free 直读):", Sk, "  σ² = I:", id_ok)
    # 限制到公共核
    Gk = matmul(ck, ckT)
    augk = [[F(0)] * (2 * dk) for _ in range(dk)]
    for i in range(dk):
        for j in range(dk):
            augk[i][j] = Gk[i][j]
        augk[i][dk + i] = F(1)
    echk2 = gaussian(augk)
    Gkinv = [[echk2[i][dk + j] for j in range(dk)] for i in range(dk)]
    Sck = matmul(Gkinv, matmul(ck, matmul(Sk, ckT)))
    print("  σ on common kernel:", Sck)
    # 特征分解 ±1
    def eigvec(Mm, val):
        Mmv = [[Mm[i][j] - (F(val) if i == j else F(0)) for j in range(dk)] for i in range(dk)]
        vv, _ = kernel_basis(gaussian(Mmv), dk)
        return vv
    vp = eigvec(Sck, +1)
    vm = eigvec(Sck, -1)
    trS = Sck[0][0] + Sck[1][1]
    detS = Sck[0][0] * Sck[1][1] - Sck[0][1] * Sck[1][0]
    print("  ker(σ−1): %d, ker(σ+1): %d   char poly: x² − %s x + %s" % (len(vp), len(vm), trS, detS))
    if len(vp) != 1 or len(vm) != 1:
        print("  !! ± 分解不符合预期 (应各 1 维)")
        return None, None

    def to_v12(alpha_ck):
        wd = matvec(ckT, alpha_ck)          # 核基坐标 (d 维)
        v12 = [F(0)] * n
        for i in range(d):
            for j in range(n):
                v12[j] += ker[i][j] * wd[i]
        return v12

    def fit_anchor(anchor_vals, r_list):
        """求 λ 泛函 φ (free3 基坐标, 3 维) 使 λ(r_i)=Σφ_k·w3_k(r_i) 匹配锚.
        正规方程 Aφ=b 精确解 (Fraction); 返回 φ 与残差列表."""
        W = [class_coords(expand_path(None, r, reps, Nv), ech3, free3) for r in r_list]
        K = len(free3)
        A = [[sum(W[i][k] * W[i][l] for i in range(len(r_list))) for l in range(K)] for k in range(K)]
        b = [sum(W[i][k] * anchor_vals[i] for i in range(len(r_list))) for k in range(K)]
        aug = [A[i] + [b[i]] for i in range(K)]
        echf = gaussian(aug)
        if len(echf) < K:
            return None, "rank<3: 锚不足决定 φ"
        phi = [F(0)] * K
        for row in reversed(echf):
            p = next((c for c in range(K + 1) if row[c] != 0), None)
            if p is None or p == K:
                continue
            s = sum(row[j] * phi[j] for j in range(p + 1, K))
            phi[p] = (row[K] - s) / row[p]
        resid = [anchor_vals[i] - sum(phi[k] * W[i][k] for k in range(K)) for i in range(len(r_list))]
        return phi, resid

    r_list = [F(1, i) for i in range(1, 12)]   # r = 1, 1/2, ..., 1/11 (锚 = M±(1/i))
    vp12 = to_v12(vp[0])
    vm12 = to_v12(vm[0])
    print("\n  plus  锚: %s" % anchors_plus)
    phi_p, resid_p = fit_anchor(anchors_plus, r_list)
    print("  plus  φ⁺ (free3 基) =", phi_p, "  残差:", resid_p)
    ok_p = phi_p is not None and all(r == 0 for r in resid_p)
    print("  plus 全命中:", ok_p)
    print("\n  minus 锚: %s" % anchors_minus)
    phi_m, resid_m = fit_anchor(anchors_minus, r_list)
    print("  minus φ⁻ (free3 基) =", phi_m, "  残差:", resid_m)
    ok_m = phi_m is not None and all(r == 0 for r in resid_m)
    print("  minus 全命中:", ok_m)
    # ± 一致性: λ⁺ 泛函应湮灭 H⁻ 方向, λ⁻ 湮灭 H⁺ 方向 (free3 坐标内积)
    if phi_p is not None and phi_m is not None:
        def free3_coords(v12):
            return class_coords(v12, ech3, free3)
        Vm = free3_coords(vm12)
        Vp = free3_coords(vp12)
        cross_p = sum(phi_p[k] * Vm[k] for k in range(len(free3)))
        cross_m = sum(phi_m[k] * Vp[k] for k in range(len(free3)))
        print("  φ⁺(H⁻) =", cross_p, " (应 0)   φ⁻(H⁺) =", cross_m, " (应 0)")
        ok_cross = (cross_p == 0 and cross_m == 0)
        print("  ± 正交一致性:", ok_cross)
    return vp12, vm12

def run389():
    """N=389, 389a1: 核 64 维 → Hecke 公共核 2 维 → σ 置换 → ± 分解 (不归一化)."""
    Nv = 389
    A_P = {2: -2, 3: -2, 5: -3, 7: -5, 11: -4, 13: -3, 17: -6, 19: 5}
    reps, idx, rel_rows = build_space(Nv, include_boundary=True)
    n = len(reps)
    ech = gaussian(rel_rows)
    ker, free = kernel_basis(ech, n)
    d = len(ker)
    print("N=%d: reps %d, ker dim %d" % (Nv, n, d))
    # Hecke 限制 + 公共核
    T = {p: restrict_to(hecke_matrix(p, reps, Nv), ker) for p in A_P}
    rows = []
    for p, a in A_P.items():
        M = [[T[p][i][j] - (F(a) if i == j else F(0)) for j in range(d)] for i in range(d)]
        rows.extend(M)
    ck, _ = kernel_basis(gaussian(rows), d)
    dk = len(ck)
    print("  common kernel dim:", dk)
    if dk != 2:
        print("  !! 公共核非 2 维 (预期 389a1)")
        return None
    ckT = [[ck[i][j] for i in range(dk)] for j in range(d)]
    # σ 置换 → 核类坐标 (free 直读)
    S = sigma_matrix(reps, Nv)
    Sk = [[matvec(S, ker[j])[f] for f in free] for j in range(d)]
    Sk = [[Sk[j][i] for j in range(d)] for i in range(d)]
    Sk2 = matmul(Sk, Sk)
    print("  σ² = I on ker:", all(Sk2[i][j] == (F(1) if i == j else F(0)) for i in range(d) for j in range(d)))
    # σ 限制到公共核
    Gk = matmul(ck, ckT)
    augk = [[F(0)] * (2 * dk) for _ in range(dk)]
    for i in range(dk):
        for j in range(dk):
            augk[i][j] = Gk[i][j]
        augk[i][dk + i] = F(1)
    echk2 = gaussian(augk)
    Gkinv = [[echk2[i][dk + j] for j in range(dk)] for i in range(dk)]
    Sck = matmul(Gkinv, matmul(ck, matmul(Sk, ckT)))
    print("  σ on common kernel:", Sck)
    # ± 特征分解
    def eigvec(Mm, val):
        Mmv = [[Mm[i][j] - (F(val) if i == j else F(0)) for j in range(dk)] for i in range(dk)]
        vv, _ = kernel_basis(gaussian(Mmv), dk)
        return vv
    vp = eigvec(Sck, +1)
    vm = eigvec(Sck, -1)
    trS = Sck[0][0] + Sck[1][1]
    detS = Sck[0][0] * Sck[1][1] - Sck[0][1] * Sck[1][0]
    print("  ker(σ−1): %d, ker(σ+1): %d   char poly: x² − %s x + %s" % (len(vp), len(vm), trS, detS))
    # 特征向量 → 核基坐标
    def to_ck_vec(alpha_ck):
        return matvec(ckT, alpha_ck)     # 公共核基坐标 → 核基坐标
    vp_ker = to_ck_vec(vp[0])
    vm_ker = to_ck_vec(vm[0])
    print("  v+ (核基坐标):", vp_ker)
    print("  v− (核基坐标):", vm_ker)
    return vp_ker, vm_ker

if __name__ == "__main__":
    # N=11, 11a1: a2=−2, a3=−1
    plus  = [F(1,5), F(-4,5), F(-3,10), F(7,10), F(6,5), F(6,5),
             F(7,10), F(-3,10), F(-4,5), F(1,5), F(0)]
    minus = [F(0), F(0), F(1,2), F(1,2), F(0), F(0),
             F(-1,2), F(-1,2), F(0), F(0), F(0)]
    run(11, {2: -2, 3: -1}, plus, minus)
    print("\n" + "=" * 60)
    run389()
