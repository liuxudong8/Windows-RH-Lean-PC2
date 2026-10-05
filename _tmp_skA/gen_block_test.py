# -*- coding: utf-8 -*-
"""gen_block_test.py —— 生成 50 项分块表达式的 native_decide 测试 + cast 测试"""
import importlib.util
spec = importlib.util.spec_from_file_location('g', r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\gen_aE5_table.py')
# 直接内联 build_a5（避免副作用跑 mpmath）
import math

def chi5(p):
    r = p % 5
    return 1 if r in (1, 4) else -1

def ap_Q(p):
    if p == 37:
        return -1
    n = 0
    for x in range(p):
        r = (4 * x * x * x - 4 * x + 1) % p
        if r == 0:
            n += 1
        elif pow(r, (p - 1) // 2, p) == 1:
            n += 2
    return p - n

def build_a5(nmax):
    a = [0] * (nmax + 1)
    a[1] = 1
    ppow = {}
    for p in range(2, nmax + 1):
        isp = True; d = 2
        while d * d <= p:
            if p % d == 0:
                isp = False; break
            d += 1
        if not isp:
            continue
        if p == 5:
            ppow[p] = {0: 1}
            continue
        if p == 37:
            ppow[p] = {k: 1 for k in range(0, 8)}
            continue
        ap = chi5(p) * ap_Q(p)
        ppow[p] = {0: 1, 1: ap}
        pk = p * p; k = 2
        while pk <= nmax:
            ppow[p][k] = ap * ppow[p][k - 1] - p * ppow[p][k - 2]
            pk *= p; k += 1
    for n in range(2, nmax + 1):
        mm = n; val = 1; p = 2
        while p * p <= mm:
            if mm % p == 0:
                e = 0
                while mm % p == 0:
                    mm //= p; e += 1
                if p == 5:
                    val *= 0
                elif p == 37:
                    val *= 1
                else:
                    val *= ppow[p][e]
            p += 1
        if mm > 1:
            if mm == 5:
                val *= 0
            elif mm == 37:
                val *= 1
            else:
                val *= ppow[mm][1]
        a[n] = val
    return a

a5 = build_a5(60)
N = 50
QM = '((8133 : ℚ) / 10000)'   # 正项底（带括号）
QP = '((8136 : ℚ) / 10000)'   # 负项底

def term(n, an):
    q = QM if an > 0 else QP
    return '(%d : ℚ) / (%d : ℚ) * %s ^ %d' % (an, n, q, n)

expr = ' +\n    '.join(term(n, a5[n]) for n in range(1, N + 1) if a5[n] != 0)

with open(r'c:\proj2\BSD\_test_block.lean', 'w', encoding='utf-8') as f:
    f.write('import Mathlib.Data.Rat.Defs\nimport Mathlib.Data.Real.Basic\nimport Mathlib.Data.Rat.Cast.Order\nimport Mathlib.Data.Rat.Cast.Lemmas\n\n')
    f.write('-- 50 项分块表达式（正项 0.8133、负项 0.8136）native_decide\n')
    f.write('example : (26765 : ℚ) / 10000 ≤\n    %s := by\n  native_decide\n\n' % expr)
    # cast 测试（小规模 3 项，显式分数）
    f.write('-- ℚ→ℝ cast 测试（3 项）\n')
    f.write('example : (20 : ℝ) / 10 ≤\n')
    f.write('    (1 : ℝ) / (1 : ℝ) * ((8133 : ℝ) / 10000) ^ 1 +\n')
    f.write('    (2 : ℝ) / (2 : ℝ) * ((8133 : ℝ) / 10000) ^ 2 +\n')
    f.write('    (3 : ℝ) / (3 : ℝ) * ((8133 : ℝ) / 10000) ^ 3 := by\n')
    f.write('  have hq : (20 : ℚ) / 10 ≤\n')
    f.write('      (1 : ℚ) / (1 : ℚ) * ((8133 : ℚ) / 10000) ^ 1 +\n')
    f.write('      (2 : ℚ) / (2 : ℚ) * ((8133 : ℚ) / 10000) ^ 2 +\n')
    f.write('      (3 : ℚ) / (3 : ℚ) * ((8133 : ℚ) / 10000) ^ 3 := by native_decide\n')
    f.write('  have hq\' := (Rat.cast_le (K := ℝ)).mpr hq\n')
    f.write('  norm_num at hq\'\n')
    f.write('  norm_num at hq\' ⊢\n')
    f.write('  exact hq\'\n\n')
    # 51 次幂 native
    f.write('-- 0.8136^51 < 1/1000 native_decide\n')
    f.write('example : ((8136 : ℚ) / 10000) ^ 51 < 1 / 1000 := by\n  native_decide\n')
print('已生成 _test_block.lean')
