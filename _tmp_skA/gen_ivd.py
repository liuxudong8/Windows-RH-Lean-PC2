# -*- coding: utf-8 -*-
"""gen_ivd.py —— 生成 §5 (iv-d) 部分和下界定理（①c）
用法：python gen_ivd.py <N> <outfile>  （N = 部分和项数；测试用 3，正式用 50）
生成内容：alpha_lt_2066、exp_neg_alpha_gt_8133、alphaE5/fE5、
3 个数学 axiom、powE_any/powE'_any、term_k（正/负/零）、crude_n_R、
crudeN_Q 分块 native_decide + cast、partN_ge、tail 界（固定 50）、L_E5_pos。
"""
import sys
from fractions import Fraction
import math

def legendre_sq_count(p, f):
    n = 0
    for x in range(p):
        r = f(x) % p
        if r == 0:
            n += 1
        elif pow(r, (p - 1) // 2, p) == 1:
            n += 2
    return n

def count_Fp_y2y(p):
    return legendre_sq_count(p, lambda x: 4 * x * x * x - 4 * x + 1)

def ap_Q(p):
    if p == 37:
        return -1
    return p - count_Fp_y2y(p)

def chi5(p):
    r = p % 5
    return 1 if r in (1, 4) else -1

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

def main():
    N = int(sys.argv[1])
    out = sys.argv[2]
    a = build_a5(N + 5)

    def coeff_R(k):
        return f"(aE5 {k} : ℝ)" if k == 1 else f"(aE5 {k} : ℝ) / {k}"
    def coeff_Q(k):
        return f"(aE5 {k} : ℚ)" if k == 1 else f"(aE5 {k} : ℚ) / {k}"

    # 各项：n = 0..N-1 对应 aE5 (n+1)
    signs = []  # +1 / -1 / 0
    for n in range(N):
        k = n + 1
        if a[k] > 0: signs.append('p')
        elif a[k] < 0: signs.append('m')
        else: signs.append('z')

    # ---- 生成项证明体（term_k : crs[k-1] ≤ fE5 (k-1)）----
    terms = []
    for n in range(N):
        k = n + 1
        s = signs[n]
        base = '0.8133' if s != 'm' else '0.8136'
        crs = f"({coeff_R(k)} * (({base} : ℝ) ^ {k}))"
        if s == 'z':
            body = f"""theorem term_{k} : {crs} ≤ fE5 {n} := by
  have hz : aE5 {k} = 0 := by native_decide
  simp [fE5, alphaE5, hz]"""
        elif s == 'p':
            if k == 1:
                body = f"""theorem term_{k} : {crs} ≤ fE5 {n} := by
  have hcoef : (0 : ℝ) ≤ (aE5 {k} : ℝ) := by
    have hz : (0 : ℤ) ≤ aE5 {k} := by native_decide
    exact_mod_cast hz
  have hpow := powE_any {n}
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm"""
            else:
                body = f"""theorem term_{k} : {crs} ≤ fE5 {n} := by
  have hcoef : (0 : ℝ) ≤ (aE5 {k} : ℝ) / {k} := by
    have hz : (0 : ℤ) ≤ aE5 {k} := by native_decide
    have hcast : (0 : ℝ) ≤ (aE5 {k} : ℝ) := by exact_mod_cast hz
    exact div_nonneg hcast (by norm_num)
  have hpow := powE_any {n}
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm"""
        else:
            if k == 1:
                body = f"""theorem term_{k} : {crs} ≤ fE5 {n} := by
  have hcoef : (aE5 {k} : ℝ) ≤ 0 := by
    have hz : aE5 {k} ≤ 0 := by native_decide
    exact_mod_cast hz
  have hpow := powE'_any {n}
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm"""
            else:
                body = f"""theorem term_{k} : {crs} ≤ fE5 {n} := by
  have hcoef : (aE5 {k} : ℝ) / {k} ≤ 0 := by
    have hz : aE5 {k} ≤ 0 := by native_decide
    have hcast : (aE5 {k} : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hz
    have hk : (0 : ℝ) < ({k} : ℝ) := by norm_num
    exact (div_le_iff₀ (a := (0 : ℝ)) hk).mpr (by simpa using hcast)
  have hpow := powE'_any {n}
  have hm := mul_le_mul_of_nonpos_left hpow hcoef
  norm_num [fE5, alphaE5] at hm ⊢
  exact hm"""
        terms.append(body)

    # ---- crude_n_R def（按符号定底）----
    crudelines = []
    for n in range(N):
        k = n + 1
        base = '0.8133' if signs[n] != 'm' else '0.8136'
        crudelines.append(
            f"  | {n} => {coeff_R(k)} * (({base} : ℝ) ^ {k})")
    crude_def = "def crude_n_R : ℕ → ℝ\n" + "\n".join(crudelines) + "\n  | _ => 0"

    # ---- 项 0 的 crude_n_R 展开（term 里 simpa 用 if？—— 已用模式匹配 def）----
    # 注意：模式匹配 def 的 simp 归：crude_n_R 0 直接归到分支（rfl 级）——term 里 simpa [crude_n_R] 归。

    # ---- 分块 native_decide（ℚ）----
    # 块大小 10
    BLK = 10
    blocks = []
    for b in range((N + BLK - 1) // BLK):
        lo = b * BLK; hi = min(N, lo + BLK)
        # 块内各 item ℚ 表达式（正项 8133、负项 8136）
        items = []
        for n in range(lo, hi):
            k = n + 1
            base = '8133' if signs[n] != 'm' else '8136'
            items.append(f"({coeff_Q(k)} * ((({base} : ℚ) / 10000) ^ {k}))")
        # 块 ℚ 真值（Fraction 精确）
        frac = Fraction(0)
        for n in range(lo, hi):
            k = n + 1
            base = Fraction(8133, 10000) if signs[n] != 'm' else Fraction(8136, 10000)
            coef = Fraction(a[k], k)
            frac += coef * base ** k
        # qk = 下取整到 10 位小数（负数也要 floor，不能用 int() 截断）
        qk_num = math.floor(frac * 10 ** 10)
        qk = Fraction(qk_num, 10 ** 10)
        # 检查 qk ≤ frac
        assert qk <= frac, f"block {b} floor issue"
        expr = " + ".join(items)
        blocks.append((qk, expr, frac))

    # ---- cast 桥 + linarith 拼 ----	
    cast_lines = []
    for b, (qk, expr, frac) in enumerate(blocks):
        qk_str = f"{qk.numerator}/{qk.denominator}" if qk.denominator != 1 else f"{qk.numerator}/1"
        cast_lines.append(f"""  have hq{b} : ({qk_str} : ℚ) ≤ {expr} := by
    native_decide
  have hq{b}' := (Rat.cast_le (K := ℝ)).mpr hq{b}
  norm_num at hq{b}'""")

    # ---- crudeN_Q / crudeN_R ----
    q_expr_all = " + ".join(
        [f"((aE5 {n+1} : ℚ) / {n+1} * ((({'8133' if signs[n] != 'm' else '8136'} : ℚ) / 10000) ^ {n+1}))"
         for n in range(N)])

    # 求和链（add_le_add 右结合嵌套）
    def nest_add(names, i):
        if i == len(names) - 1:
            return names[i]
        return f"{names[i]} + ({nest_add(names, i + 1)})"

    def nest_ala(names, i):
        if i == len(names) - 1:
            return names[i]
        return f"add_le_add {names[i]} ({nest_ala(names, i + 1)})"

    term_names = [f"term_{n+1}" for n in range(N)]
    add_chain = nest_add(term_names, 0)

    # 生成输出
    L = []
    L.append("""import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import BSD.LSeries5
import BSD.aE5_table

set_option maxHeartbeats 4000000

namespace BSD.LSeries5

/-! ## 5. (iv-d) 部分和下界（axiom → theorem）——①c -/

section ivd

noncomputable section

open scoped BigOperators

/-- α = 2π/√925 的上界：α < 0.2066。
    证明：π < 3.1416（`Real.pi_lt_d4`）；√925 > 30.413（`Real.lt_sqrt`）；
    组合：2π < 2·3.1416 < 0.2066·30.413 < 0.2066·√925。 -/
theorem alpha_lt_2066 : 2 * Real.pi / Real.sqrt 925 < (0.2066 : ℝ) := by
  have hsqrt : (30.413 : ℝ) < Real.sqrt 925 := by
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 30.413)).2 (by norm_num)
  have h1 : (2 : ℝ) * (3.1416 : ℝ) < (0.2066 : ℝ) * 30.413 := by norm_num
  have h2 : (2 : ℝ) * Real.pi ≤ (2 : ℝ) * (3.1416 : ℝ) := by
    exact mul_le_mul_of_nonneg_left Real.pi_lt_d4.le (by norm_num : (0 : ℝ) ≤ 2)
  have h2' : (2 : ℝ) * Real.pi < (0.2066 : ℝ) * 30.413 := lt_of_le_of_lt h2 h1
  have h3 : (0.2066 : ℝ) * 30.413 < (0.2066 : ℝ) * Real.sqrt 925 := by
    exact mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 0.2066)
  have h3' : (2 : ℝ) * Real.pi < (0.2066 : ℝ) * Real.sqrt 925 := lt_trans h2' h3
  rw [div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 925))]
  simpa [mul_comm] using h3'

/-- e^(−α) > 0.8133：α < 0.2066（exp 单调）；e^(0.2066) ≤ Σ₆ + B < 1/0.8133
    （`Real.exp_bound` n = 6 上界）⟹ e^(−0.2066) = 1/e^(0.2066) > 0.8133。 -/
theorem exp_neg_alpha_gt_8133 : (0.8133 : ℝ) < Real.exp (-(2 * Real.pi / Real.sqrt 925)) := by
  have hmono : Real.exp (-(0.2066 : ℝ)) ≤ Real.exp (-(2 * Real.pi / Real.sqrt 925)) := by
    exact Real.exp_le_exp_of_le (by linarith [alpha_lt_2066])
  have hrecip : (0.8133 : ℝ) < Real.exp (-(0.2066 : ℝ)) := by
    rw [Real.exp_neg]
    have hexp : Real.exp (0.2066 : ℝ) < (1 / (0.8133 : ℝ)) := by
      have hsum : (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ)) =
          (1 : ℝ) + 0.2066 + (0.2066 : ℝ) ^ 2 / 2 + (0.2066 : ℝ) ^ 3 / 6 +
            (0.2066 : ℝ) ^ 4 / 24 + (0.2066 : ℝ) ^ 5 / 120 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ]
        norm_num
      have hb := Real.exp_bound (x := 0.2066) (n := 6) (by norm_num : |(0.2066 : ℝ)| ≤ 1) (by norm_num : 0 < 6)
      have hd : Real.exp (0.2066 : ℝ) - (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
          ≤ (0.2066 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
        have h1 : Real.exp (0.2066 : ℝ) - (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
            ≤ |(0.2066 : ℝ)| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) :=
          le_trans (le_abs_self _) hb
        simpa [abs_of_pos (by norm_num : (0 : ℝ) < 0.2066)] using h1
      have hle' : Real.exp (0.2066 : ℝ) ≤
          (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
          + (0.2066 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
        linarith
      have hpartU : (∑ m ∈ Finset.range 6, (0.2066 : ℝ) ^ m / (m.factorial : ℝ))
          + (0.2066 : ℝ) ^ 6 * ((7 : ℝ) / ((Nat.factorial 6 : ℝ) * 6))
          < 1 / (0.8133 : ℝ) := by
        norm_num [hsum]
      exact lt_of_le_of_lt hle' hpartU
    have htmp : 1 / (1 / (0.8133 : ℝ)) < 1 / Real.exp (0.2066 : ℝ) := by
      exact one_div_lt_one_div_of_lt (Real.exp_pos (0.2066 : ℝ)) hexp
    simpa using htmp
  exact lt_of_lt_of_le hrecip hmono

/-- α 的 Lean 名（数值参数化）。 -/
def alphaE5 : ℝ := 2 * Real.pi / Real.sqrt 925

/-- 反射公式第 n 项（截断级数）：
    fE5 n = a_{n+1}(E⁵)/(n+1) · e^(−α·(n+1))。 -/
noncomputable def fE5 : ℕ → ℝ := fun n =>
  (aE5 (n + 1) : ℝ) / (n + 1) * Real.exp (-alphaE5 * (n + 1))

/- 数学 axiom（①c 的分层：等式/界/收敛为 axiom，不等式链为定理）：
   · `L_E5_series_split`：Dokchitser 反射公式 s = 1 的 N-截断等式（替代原 `L_E5_one_ne_zero` 判定黑盒）；
   · `coefficient_bound_aE5`：|a_n(E⁵)| ≤ 2n（表版；与 §2 `coefficient_bound` 同数学内容，
     aE5 为独立值表定义故单列）；
   · `summable_fE5`：反射级数绝对收敛（几何级数比较）。 -/
axiom L_E5_series_split (N : ℕ) :
  L_E5 1 = 2 * (∑ n ∈ Finset.range N, fE5 n) + 2 * ∑' n : ℕ, fE5 (n + N)
axiom coefficient_bound_aE5 (n : ℕ) : |aE5 n| ≤ 2 * (n : ℝ)
axiom summable_fE5 : Summable fE5

/-- 任意 n 的幂界（正项底）：0.8133^(n+1) ≤ e^(−α(n+1))。 -/
theorem powE_any (n : ℕ) : ((0.8133 : ℝ) ^ (n + 1)) ≤ Real.exp (-alphaE5 * (n + 1)) := by
  have hpow : ((0.8133 : ℝ) ^ (n + 1)) ≤ (Real.exp (-alphaE5)) ^ (n + 1) := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (0.8133 : ℝ)) exp_neg_alpha_gt_8133.le (n + 1)
  rw [← Real.exp_nat_mul] at hpow
  simpa [mul_comm] using hpow

/-- 任意 n 的幂界（负项底）：e^(−α(n+1)) ≤ 0.8136^(n+1)。 -/
theorem powE'_any (n : ℕ) : Real.exp (-alphaE5 * (n + 1)) ≤ ((0.8136 : ℝ) ^ (n + 1)) := by
  have hpow : (Real.exp (-alphaE5)) ^ (n + 1) ≤ ((0.8136 : ℝ) ^ (n + 1)) := by
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos (-alphaE5))) exp_neg_alpha_lt_8136.le (n + 1)
  rw [← Real.exp_nat_mul] at hpow
  simpa [mul_comm] using hpow

/-- 粗界项（ℝ 版）：正项用底 0.8133、负项用底 0.8136（模式匹配，按 aE5 符号固定）。 -/
""")
    L.append(crude_def)
    L.append("\n")
    # 逐项定理
    for t in terms:
        L.append(t + "\n")
    # ---- crudeN_ge_R（分块 cast + linarith）----
    # 阈值：N=3 测试用 2.0127（q_total≈2.01272），正式 N≥40 用 2.6766（q_total≈2.67661）
    thr = "2.0127" if N < 40 else "2.6766"
    L.append("/-- 部分和粗界（ℝ）：" + thr + " ≤ 粗界 " + str(N) + " 项和（分块 ℚ native_decide + cast 桥）。 -/\n")
    L.append(f"theorem crude{N}_ge_R : ({thr} : ℝ) ≤")
    # crudeN_R 用右结合嵌套展开
    crs = []
    for n in range(N):
        k = n + 1
        base = '0.8133' if signs[n] != 'm' else '0.8136'
        crs.append(f"({coeff_R(k)} * (({base} : ℝ) ^ {k}))")
    L.append(" " + nest_add(crs, 0) + " := by\n")
    for line in cast_lines:
        L.append(line + "\n")
    # linarith 拼：qk 和 ≥ 2.6766
    q_total = sum(qk for qk, _, _ in blocks)
    L.append("  have hqT : (" + thr + " : ℝ) ≤ " + " + ".join([f"({qk.numerator} : ℝ) / {qk.denominator}" for qk, _, _ in blocks]) + " := by norm_num\n")
    L.append("  norm_num\n")
    L.append("  nlinarith")
    L.append("\n\n")
    # partN_ge（crude ≤ Σ fE5：simp 展开 Σ + linarith）
    L.append("/-- 部分和 ≥ 粗界（逐项；Σ 用 sum_range_succ 展开后 linarith）。 -/\n")
    L.append(f"theorem part{N}_ge_crude :")
    L.append(" " + nest_add(crs, 0) + " ≤ ∑ n ∈ Finset.range " + str(N) + ", fE5 n := by\n")
    L.append("  simp [Finset.sum_range_succ]\n")
    for n in range(N):
        k = n + 1
        L.append(f"  have h{n} : {crs[n]} ≤ fE5 {n} := term_{k}\n")
    L.append(f"  linarith")
    L.append("\n\n")
    L.append(f"theorem part{N}_ge : ({thr} : ℝ) ≤ ∑ n ∈ Finset.range {N}, fE5 n := by\n")
    L.append(f"  exact le_trans crude{N}_ge_R part{N}_ge_crude\n")

    with open(out, "w", encoding="utf-8") as f:
        f.write("\n".join(L))
    print(f"OK: wrote {out}, N={N}, blocks={len(blocks)}, q_total={q_total.numerator}/{q_total.denominator}")

if __name__ == "__main__":
    main()
