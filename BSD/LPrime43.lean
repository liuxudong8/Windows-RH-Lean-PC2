import BSD.LPrime
import BSD.aE_table_43

set_option maxHeartbeats 4000000

/-!
# LPrime43: L′(43a1,1) 的严格正性（N = 43，ε = −1 反射公式一阶导）

E = 43a1（y²+xy+y = x³+x²），N = 43，秩 1。目标：逐曲线闭证
`lprime1_43 > 0`（秩 1 BSD 反向的 L′(E,1) 分量），供 (1,0) 排除层实例。

与 37a1（BSD.LPrime）的差异：b₁(43) = 2π/√43 ≈ 0.958 < 1
（37a1 的 b₁ ≈ 1.033 > 1）。E₁ 下界段链 [1.04, 8.04] 依然适用
（只需 b₁ < 1.04，0.958 < 1.04 ✓）；几何尾用 b₁ > 0.95 的衰减率
（e^{−0.95m}，比 37a1 的 e^{−1.03m} 慢但收敛）。

数值校准（calib43_float.py，2026-10-11）：L′(43a1,1) ≈ 0.343524，
部分和 3 项 ≈ 0.406，尾（n ≥ 4）≤ 0.0215 —— part3_lower 0.0417 有裕度。

分层（仿 BSD.LPrime）：
1. aₙ 表（aE_table_43.lean，200 项穷举点计数）+ |aₙ| ≤ 2n（native_decide）。
2. E₁ 界：E₁(b) ≤ e^{−b}/b（BSD.LPrime.E1_le 复用）；段链下界 0.1337（复用
   BSD.LPrime 的 L0_ge…L13_ge + seg_chain_ge，truncation 用 b₁(43) < 1.04）。
3. 反射公式：lprime1_43 = 2·Σ aₙ/n·E₁(2πn/√43)（挂账 axiom 级，同 37a1 的
   lprime1_series 状态——mathlib 无自守 L 理论）。
4. 部分和前三项 + 几何尾 ⟹ lprime1_43 > 0（真定理）。
-/

namespace BSD.LPrime43

noncomputable section

open scoped BigOperators
open MeasureTheory

/-! ## 1. aₙ 表（E = 43a1） -/

/-- E = 43a1 的 aₙ（n ≤ 100 查表，表外为 0）。 -/
def aE43 (n : ℕ) : ℤ := if n ≤ 100 then aE_raw_43 n else 0

/-- |aₙ| ≤ 2n（n ≤ 100，interval_cases 逐项 native_decide 查表核验）。 -/
theorem aE43_bound (m : ℕ) (hm : m ≤ 100) : |aE43 m| ≤ 2 * (m : ℤ) := by
  rw [aE43, if_pos hm]
  interval_cases m <;> native_decide

/-- aE43 全下标界（m > 100 时 aE43 m = 0，自动成立）。 -/
theorem aE43_bound_all (m : ℕ) : |aE43 m| ≤ 2 * (m : ℤ) := by
  by_cases hm : m ≤ 100
  · exact aE43_bound m hm
  · dsimp [aE43]
    rw [if_neg hm]
    norm_num

/-! ## 2. bₙ 与 √43 界 -/

/-- bₙ = 2πn/√43（ℚ 端 exp 衰减常数）。 -/
def bn43 (n : ℕ) : ℝ := 2 * Real.pi * (n : ℝ) / Real.sqrt 43

/-- √43 < 6.57（6.57² = 43.1649 > 43）。 -/
lemma sqrt43_lt_657 : Real.sqrt 43 < (6.57 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 6.57)]
  norm_num [show (6.57 : ℝ) = (657 : ℝ) / 100 by norm_num]

/-- √43 > 6.55（6.55² = 42.9025 < 43）。 -/
lemma sqrt43_gt_655 : (6.55 : ℝ) < Real.sqrt 43 := by
  exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 6.55)).2 (by norm_num)

/-- b₁(43) > 0.95：0.95·√43 < 0.95·6.57 = 6.2415 < 6.283 < 2π。 -/
theorem b1_43_gt_095 : (0.95 : ℝ) < bn43 1 := by
  have h1 : (0.95 : ℝ) * Real.sqrt 43 < (0.95 * 6.57 : ℝ) := by
    exact mul_lt_mul_of_pos_left sqrt43_lt_657 (by norm_num : (0 : ℝ) < 0.95)
  have h2 : (0.95 * 6.57 : ℝ) < 2 * Real.pi := by
    have h3 : (0.95 * 6.57 : ℝ) < 2 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 2))
  have h4 : (0.95 : ℝ) * Real.sqrt 43 < 2 * Real.pi := lt_trans h1 h2
  have hbn : bn43 1 = 2 * Real.pi / Real.sqrt 43 := by
    unfold bn43
    ring
  rw [hbn]
  exact (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 43))).mpr h4

/-- b₁(43) < 1.04：2π < 6.2832 < 6.812 = 1.04·6.55 < 1.04·√43。 -/
theorem b1_43_lt_104 : bn43 1 < (1.04 : ℝ) := by
  have h1 : (2 : ℝ) * (3.1416 : ℝ) < (1.04 : ℝ) * 6.55 := by norm_num
  have h2 : (2 : ℝ) * Real.pi ≤ (2 : ℝ) * (3.1416 : ℝ) := by
    exact mul_le_mul_of_nonneg_left Real.pi_lt_d4.le (by norm_num : (0 : ℝ) ≤ 2)
  have h2' : (2 : ℝ) * Real.pi < (1.04 : ℝ) * 6.55 := lt_of_le_of_lt h2 h1
  have h3 : (1.04 : ℝ) * 6.55 < (1.04 : ℝ) * Real.sqrt 43 := by
    exact mul_lt_mul_of_pos_left sqrt43_gt_655 (by norm_num : (0 : ℝ) < 1.04)
  have h3' : (2 : ℝ) * Real.pi < (1.04 : ℝ) * Real.sqrt 43 := lt_trans h2' h3
  have hbn : bn43 1 = 2 * Real.pi / Real.sqrt 43 := by
    unfold bn43
    ring
  rw [hbn]
  exact (div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 43))).mpr h3'

/-- b₁(43) > 0。 -/
theorem b1_43_pos : (0 : ℝ) < bn43 1 := by
  exact lt_trans (by norm_num : (0 : ℝ) < 0.95) b1_43_gt_095

/-- bₙ(43) = n·b₁(43)。 -/
lemma bn43_mul (n : ℕ) : bn43 n = (n : ℝ) * bn43 1 := by
  unfold bn43
  ring

/-- bₙ(43) ≥ n·0.95（b₁(43) > 0.95 的乘性）。 -/
theorem bn43_ge_095m (m : ℕ) : (m : ℝ) * 0.95 ≤ bn43 m := by
  have hb1 : (0.95 : ℝ) ≤ bn43 1 := b1_43_gt_095.le
  calc
    (m : ℝ) * 0.95 ≤ (m : ℝ) * bn43 1 := by
      exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = bn43 m := by
      dsimp [bn43]
      ring

/-- m ≥ 4 ⟹ bₙ(43) ≥ 4·0.95。 -/
lemma bn43_ge_4c (m : ℕ) (hm4 : 4 ≤ m) : (4 : ℝ) * 0.95 ≤ bn43 m := by
  calc
    (4 : ℝ) * 0.95 ≤ (m : ℝ) * 0.95 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm4) (by norm_num : (0 : ℝ) ≤ 0.95)
    _ ≤ bn43 m := bn43_ge_095m m

/-! ## 3. 反射公式一阶导（声明层） -/

/-- L′(43a1,1) 的级数形态：lprime1_43 = 2Σ aₙ/n·E₁(2πn/√43)。
    依据：N = 43，根数 ε = −1（奇符号），一阶导 Mellin 展开——与
    BSD.LPrime.lprime1 同源；数学身份为挂账 axiom（mathlib 无自守 L 理论）。 -/
noncomputable def lprime1_43 : ℝ :=
  2 * ∑' n : ℕ, (aE43 (n + 1) : ℝ) / (n + 1) * LPrime.E1 (bn43 (n + 1))

/-! ## 4. E₁ 数值界（43a1 特异，exp_bound 闭合） -/

/-- e^{−0.91} ≤ 0.4026（exp_bound n = 8）。 -/
theorem exp_neg_091_le : Real.exp (-(0.91 : ℝ)) ≤ (0.4026 : ℝ) := by
  have hb := Real.exp_bound (x := (-(0.91 : ℝ))) (n := 8)
    (by norm_num : |(-(0.91 : ℝ))| ≤ 1) (by norm_num : 0 < 8)
  have hd : |Real.exp (-(0.91 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.91 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
      |(-(0.91 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := hb
  have hd2 : Real.exp (-(0.91 : ℝ)) ≤ (∑ m ∈ Finset.range 8, (-(0.91 : ℝ)) ^ m / (m.factorial : ℝ)) +
      |(-(0.91 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by
    have h1 : Real.exp (-(0.91 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.91 : ℝ)) ^ m / (m.factorial : ℝ)) ≤
        |(-(0.91 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) :=
      le_trans (le_abs_self _) hd
    linarith
  have hsum : (∑ m ∈ Finset.range 8, (-(0.91 : ℝ)) ^ m / (m.factorial : ℝ)) ≤ (0.40253 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hbnd : (0.40253 : ℝ) + |(-(0.91 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) ≤ (0.4026 : ℝ) := by
    norm_num
  linarith

/-- e^{−0.86} ≤ 0.4235（exp_bound n = 8）。 -/
theorem exp_neg_086_le : Real.exp (-(0.86 : ℝ)) ≤ (0.4235 : ℝ) := by
  have hb := Real.exp_bound (x := (-(0.86 : ℝ))) (n := 8)
    (by norm_num : |(-(0.86 : ℝ))| ≤ 1) (by norm_num : 0 < 8)
  have hd : |Real.exp (-(0.86 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.86 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
      |(-(0.86 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := hb
  have hd2 : Real.exp (-(0.86 : ℝ)) ≤ (∑ m ∈ Finset.range 8, (-(0.86 : ℝ)) ^ m / (m.factorial : ℝ)) +
      |(-(0.86 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by
    have h1 : Real.exp (-(0.86 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.86 : ℝ)) ^ m / (m.factorial : ℝ)) ≤
        |(-(0.86 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) :=
      le_trans (le_abs_self _) hd
    linarith
  have hsum : (∑ m ∈ Finset.range 8, (-(0.86 : ℝ)) ^ m / (m.factorial : ℝ)) ≤ (0.4233 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hbnd : (0.4233 : ℝ) + |(-(0.86 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) ≤ (0.4235 : ℝ) := by
    norm_num
  linarith

/-- e^{−0.95} ≤ 0.3869（= e^{−1}·e^{0.05}，exp_bound 链）。 -/
theorem exp_neg_095_le : Real.exp (-(0.95 : ℝ)) ≤ (0.3869 : ℝ) := by
  have h1 : Real.exp (-(0.95 : ℝ)) = Real.exp (-1) * Real.exp (0.05 : ℝ) := by
    have hsplit : -(0.95 : ℝ) = -1 + (0.05 : ℝ) := by norm_num
    rw [hsplit, Real.exp_add]
  have h2a : Real.exp (-1) * Real.exp (0.05 : ℝ) ≤ (0.36790 : ℝ) * Real.exp (0.05 : ℝ) := by
    exact mul_le_mul_of_nonneg_right LPrime.exp_neg_one_le (by positivity)
  have h2b : (0.36790 : ℝ) * Real.exp (0.05 : ℝ) ≤ (0.36790 : ℝ) * (1.0513 : ℝ) := by
    have hpos05 : Real.exp (0.05 : ℝ) ≤ (1.0513 : ℝ) := by
      have hb := Real.exp_bound (x := (0.05 : ℝ)) (n := 6)
        (by norm_num : |(0.05 : ℝ)| ≤ 1) (by norm_num : 0 < 6)
      have hd : |Real.exp (0.05 : ℝ) - (∑ m ∈ Finset.range 6, (0.05 : ℝ) ^ m / (m.factorial : ℝ))| ≤
          |(0.05 : ℝ)| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := hb
      have hd2 : Real.exp (0.05 : ℝ) ≤ (∑ m ∈ Finset.range 6, (0.05 : ℝ) ^ m / (m.factorial : ℝ)) +
          |(0.05 : ℝ)| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := by
        have h1 : Real.exp (0.05 : ℝ) - (∑ m ∈ Finset.range 6, (0.05 : ℝ) ^ m / (m.factorial : ℝ)) ≤
            |(0.05 : ℝ)| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) :=
          le_trans (le_abs_self _) hd
        linarith
      have hsum : (∑ m ∈ Finset.range 6, (0.05 : ℝ) ^ m / (m.factorial : ℝ)) ≤ (1.05128 : ℝ) := by
        norm_num [Finset.sum_range_succ]
      have hbnd : (1.05128 : ℝ) + |(0.05 : ℝ)| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) ≤ (1.0513 : ℝ) := by
        norm_num
      linarith
    exact mul_le_mul_of_nonneg_left hpos05 (by norm_num : (0 : ℝ) ≤ 0.36790)
  have h2 : Real.exp (-1) * Real.exp (0.05 : ℝ) ≤ (0.36790 : ℝ) * (1.0513 : ℝ) := le_trans h2a h2b
  have h3 : (0.36790 : ℝ) * (1.0513 : ℝ) ≤ (0.3869 : ℝ) := by norm_num
  rw [h1]
  exact le_trans h2 h3

/-- e^{−3.8} ≤ 0.0224（= e^{−1}·e^{−1}·e^{−1}·e^{−0.8}，exp_bound 链）。 -/
theorem exp_neg_38_le : Real.exp (-(3.8 : ℝ)) ≤ (0.0224 : ℝ) := by
  have hsplit : -(3.8 : ℝ) = -1 + (-1) + (-1) + (-(0.8 : ℝ)) := by norm_num
  rw [hsplit]
  rw [Real.exp_add]
  rw [Real.exp_add]
  rw [Real.exp_add]
  have he08 : Real.exp (-(0.8 : ℝ)) ≤ (0.4495 : ℝ) := by
    have hb := Real.exp_bound (x := (-(0.8 : ℝ))) (n := 8)
      (by norm_num : |(-(0.8 : ℝ))| ≤ 1) (by norm_num : 0 < 8)
    have hd : |Real.exp (-(0.8 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.8 : ℝ)) ^ m / (m.factorial : ℝ))| ≤
        |(-(0.8 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := hb
    have hd2 : Real.exp (-(0.8 : ℝ)) ≤ (∑ m ∈ Finset.range 8, (-(0.8 : ℝ)) ^ m / (m.factorial : ℝ)) +
        |(-(0.8 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by
      have h1 : Real.exp (-(0.8 : ℝ)) - (∑ m ∈ Finset.range 8, (-(0.8 : ℝ)) ^ m / (m.factorial : ℝ)) ≤
          |(-(0.8 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) :=
        le_trans (le_abs_self _) hd
      linarith
    have hsum : (∑ m ∈ Finset.range 8, (-(0.8 : ℝ)) ^ m / (m.factorial : ℝ)) ≤ (0.44933 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    have hbnd : (0.44933 : ℝ) + |(-(0.8 : ℝ))| ^ 8 * ((Nat.succ 8 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) ≤ (0.4495 : ℝ) := by
      norm_num
    linarith
  have h1 : Real.exp (-1) * Real.exp (-(0.8 : ℝ)) ≤ (0.36790 : ℝ) * (0.4495 : ℝ) := by
    exact mul_le_mul LPrime.exp_neg_one_le he08 (by positivity) (by positivity)
  have h2 : Real.exp (-1) * (Real.exp (-1) * Real.exp (-(0.8 : ℝ))) ≤
      (0.36790 : ℝ) * ((0.36790 : ℝ) * (0.4495 : ℝ)) := by
    exact mul_le_mul LPrime.exp_neg_one_le h1 (by positivity) (by positivity)
  have h3 : Real.exp (-1) * (Real.exp (-1) * (Real.exp (-1) * Real.exp (-(0.8 : ℝ)))) ≤
      (0.36790 : ℝ) * ((0.36790 : ℝ) * ((0.36790 : ℝ) * (0.4495 : ℝ))) := by
    exact mul_le_mul LPrime.exp_neg_one_le h2 (by positivity) (by positivity)
  have hval : (0.36790 : ℝ) * ((0.36790 : ℝ) * ((0.36790 : ℝ) * (0.4495 : ℝ))) ≤ (0.0224 : ℝ) := by
    norm_num
  simpa [mul_assoc] using (le_trans h3 hval)

/-- e^{−t}/t 在 (b₁(43), ∞) 上可积（b₁(43) > 0 情形；37a1 的 f_integrableOn_Ioi 需 c > 1，43a1 的 b₁ ≈ 0.958 < 1 不适用）。
    控制：t ≥ b₁ ⟹ f(t) ≤ e^{−t}/b₁，且 e^{−t} 在 (b₁,∞) 可积。 -/
lemma f43_integrableOn_Ioi : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi (bn43 1)) := by
  have hb : 0 < bn43 1 := b1_43_pos
  refine Integrable.mono' (g := fun t : ℝ => Real.exp (-t) / (bn43 1)) ?_ ?_ ?_
  · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (integrableOn_exp_neg_Ioi (bn43 1)).const_mul ((bn43 1)⁻¹)
  · exact (LPrime.cont_div (bn43 1) hb).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := lt_trans hb ht
    have htb : bn43 1 ≤ t := le_of_lt ht
    have hnonneg : 0 ≤ Real.exp (-t) / t := div_nonneg (le_of_lt (Real.exp_pos (-t))) (le_of_lt ht_pos)
    have hpt : Real.exp (-t) / t ≤ Real.exp (-t) / (bn43 1) := LPrime.pt_le hb htb
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpt

/-! ## 4.1 E₁(b₁(43)) 下界：0.1337（段链 [1.04, 8.04]，b₁ < 1.04 截断） -/

/-- E₁(b₁(43)) 下界：0.1337 ≤ E₁(bn43 1)。
    段链（Σ 0.5·c_k/r_k ≥ 0.1337，BSD.LPrime 的 L0_ge…L13_ge 复用）+
    truncation [1.04, 8.04] ⊆ (b₁(43), ∞)（b₁(43) < 1.04）。 -/
theorem E1_b1_43_ge : (0.1337 : ℝ) ≤ LPrime.E1 (bn43 1) := by
  let r : ℕ → ℝ := fun k => (1.04 : ℝ) + (k : ℝ) * 0.5 + 0.5
  let c : ℕ → ℝ := fun k =>
    match k with
    | 0 => 0.214362 | 1 => 0.130009 | 2 => 0.078852 | 3 => 0.047822
    | 4 => 0.029004 | 5 => 0.017589 | 6 => 0.010666 | 7 => 0.006467
    | 8 => 0.003921 | 9 => 0.002376 | 10 => 0.001440 | 11 => 0.000871
    | 12 => 0.000527 | _ => 0.000318
  have hr : ∀ k, r k = (1.04 : ℝ) + (k : ℝ) * 0.5 + 0.5 := by intro k; rfl
  have hc : ∀ k < 14, c k ≤ Real.exp (-(r k)) := by
    intro k hk
    interval_cases k
    · norm_num [c, r]; have h := LPrime.L0_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L1_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L2_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L3_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L4_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L5_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L6_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L7_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L8_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L9_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L10_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L11_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L12_ge; norm_num at h ⊢; exact h
    · norm_num [c, r]; have h := LPrime.L13_ge; norm_num at h ⊢; exact h
  have htrunc : (∫ t in Set.Icc (1.04 : ℝ) (8.04 : ℝ), Real.exp (-t) / t) ≤ LPrime.E1 (bn43 1) := by
    rw [LPrime.E1]
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    refine integral_mono_ae ?_ ?_ ?_
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (LPrime.f_integrableOn_Icc (a := 1.04) (by norm_num : (1 : ℝ) < 1.04))
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr f43_integrableOn_Ioi
    · filter_upwards with t
      by_cases ht : t ∈ Set.Icc (1.04 : ℝ) (8.04 : ℝ)
      · have hti : t ∈ Set.Ioi (bn43 1) := by
          have htx : (1.04 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
          exact lt_of_lt_of_le (by simpa [bn43] using b1_43_lt_104) htx
        simp [Set.indicator, ht, hti]
      · simp [Set.indicator, ht]
        by_cases h1 : t ∈ Set.Ioi (bn43 1)
        · have hbn1 : (0 : ℝ) < bn43 1 := b1_43_pos
          have ht0 : 0 < t := lt_trans hbn1 (Set.mem_Ioi.mp h1)
          have hle : (0 : ℝ) ≤ Real.exp (-t) / t := div_nonneg (by positivity) (le_of_lt ht0)
          have hle' : (0 : ℝ) ≤ if bn43 1 < t then Real.exp (-t) / t else 0 := by
            rw [if_pos (Set.mem_Ioi.mp h1)]
            exact hle
          simpa [Set.indicator, ht] using hle'
        · have hneg : ¬ bn43 1 < t := by
            intro h
            exact h1 (Set.mem_Ioi.mpr h)
          have hle0 : (0 : ℝ) ≤ if bn43 1 < t then Real.exp (-t) / t else 0 := by
            rw [if_neg hneg]
          simpa [Set.indicator, ht] using hle0
  have hchain : (∑ k ∈ Finset.range 14, 0.5 * (c k) / (r k)) ≤
      ∫ t in Set.Icc (1.04 : ℝ) (8.04 : ℝ), Real.exp (-t) / t := by
    have hseq := LPrime.seg_chain_ge (a := 1.04) (by norm_num : (1 : ℝ) < 1.04) 13 hr hc
    rw [show (8.04 : ℝ) = r 13 by norm_num [hr]]
    exact hseq
  have hsum : (0.1337 : ℝ) ≤ ∑ k ∈ Finset.range 14, 0.5 * (c k) / (r k) := by
    norm_num [Finset.sum_range_succ, c, r, hr]
  exact le_trans (le_trans hsum hchain) htrunc

/-! ## 4.2 E₁(b₂(43))、E₁(b₃(43)) 上界 -/

/-- b₂(43) ≥ 1.91：4π/√43 ≥ 4·3.1415/6.57 = 1.9126 > 1.91。 -/
lemma b2_43_ge_191 : (1.91 : ℝ) ≤ bn43 2 := by
  have h1 : (1.91 : ℝ) * Real.sqrt 43 < (1.91 * 6.57 : ℝ) := by
    exact mul_lt_mul_of_pos_left sqrt43_lt_657 (by norm_num : (0 : ℝ) < 1.91)
  have h2 : (1.91 * 6.57 : ℝ) < 4 * Real.pi := by
    have h3 : (1.91 * 6.57 : ℝ) < 4 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 4))
  have h4 : (1.91 : ℝ) * Real.sqrt 43 < 4 * Real.pi := lt_trans h1 h2
  have hle : (1.91 : ℝ) * Real.sqrt 43 ≤ 4 * Real.pi := h4.le
  have hbn : bn43 2 = 4 * Real.pi / Real.sqrt 43 := by
    unfold bn43
    ring
  rw [hbn]
  exact (le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 43))).mpr hle

/-- E₁(b₂(43)) ≤ 0.078：E₁ ≤ e^{−b}/b ≤ e^{−1.91}/1.91（e^{−1.91} = e^{−1}·e^{−0.91}）。 -/
theorem E1_b2_43_le : LPrime.E1 (bn43 2) ≤ (0.078 : ℝ) := by
  have hb2pos : 0 < bn43 2 := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1.91) b2_43_ge_191
  have hE : LPrime.E1 (bn43 2) ≤ Real.exp (-bn43 2) / bn43 2 := LPrime.E1_le (bn43 2) hb2pos
  have he191 : Real.exp (-(1.91 : ℝ)) ≤ (0.1482 : ℝ) := by
    have hsplit : -(1.91 : ℝ) = -1 + (-(0.91 : ℝ)) := by norm_num
    rw [hsplit, Real.exp_add]
    calc
      Real.exp (-1) * Real.exp (-(0.91 : ℝ)) ≤ (0.36790 : ℝ) * Real.exp (-(0.91 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right LPrime.exp_neg_one_le (by positivity)
      _ ≤ (0.36790 : ℝ) * (0.4026 : ℝ) := by
        exact mul_le_mul_of_nonneg_left exp_neg_091_le (by norm_num : (0 : ℝ) ≤ 0.36790)
      _ ≤ (0.1482 : ℝ) := by norm_num
  have hmono : Real.exp (-bn43 2) ≤ Real.exp (-(1.91 : ℝ)) := by
    exact Real.exp_le_exp_of_le (by linarith [b2_43_ge_191])
  have hdiv : Real.exp (-(1.91 : ℝ)) / bn43 2 ≤ Real.exp (-(1.91 : ℝ)) / (1.91 : ℝ) := by
    have hb : bn43 2 ≥ (1.91 : ℝ) := b2_43_ge_191
    have hpos : (0 : ℝ) < 1.91 := by norm_num
    have hinv : (bn43 2)⁻¹ ≤ (1.91 : ℝ)⁻¹ := by
      simpa [one_div] using (one_div_le_one_div_of_le hpos hb)
    exact mul_le_mul_of_nonneg_left hinv (le_of_lt (Real.exp_pos (-(1.91 : ℝ))))
  have hfinal : Real.exp (-(1.91 : ℝ)) / (1.91 : ℝ) ≤ (0.078 : ℝ) := by
    have htop : Real.exp (-(1.91 : ℝ)) ≤ (0.1482 : ℝ) := he191
    have hdivv : (0.1482 : ℝ) / (1.91 : ℝ) ≤ (0.078 : ℝ) := by norm_num
    exact (div_le_div_of_nonneg_right htop (by norm_num : (0 : ℝ) ≤ 1.91)).trans hdivv
  calc
    LPrime.E1 (bn43 2) ≤ Real.exp (-bn43 2) / bn43 2 := hE
    _ ≤ Real.exp (-(1.91 : ℝ)) / bn43 2 := by
      exact div_le_div_of_nonneg_right hmono (le_of_lt hb2pos)
    _ ≤ Real.exp (-(1.91 : ℝ)) / (1.91 : ℝ) := hdiv
    _ ≤ (0.078 : ℝ) := hfinal

/-- b₃(43) ≥ 2.86：6π/√43 ≥ 6·3.1415/6.57 = 2.8690 > 2.86。 -/
lemma b3_43_ge_286 : (2.86 : ℝ) ≤ bn43 3 := by
  have h1 : (2.86 : ℝ) * Real.sqrt 43 < (2.86 * 6.57 : ℝ) := by
    exact mul_lt_mul_of_pos_left sqrt43_lt_657 (by norm_num : (0 : ℝ) < 2.86)
  have h2 : (2.86 * 6.57 : ℝ) < 6 * Real.pi := by
    have h3 : (2.86 * 6.57 : ℝ) < 6 * (3.1415 : ℝ) := by norm_num
    exact lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_left Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 6))
  have h4 : (2.86 : ℝ) * Real.sqrt 43 < 6 * Real.pi := lt_trans h1 h2
  have hle : (2.86 : ℝ) * Real.sqrt 43 ≤ 6 * Real.pi := h4.le
  have hbn : bn43 3 = 6 * Real.pi / Real.sqrt 43 := by
    unfold bn43
    ring
  rw [hbn]
  exact (le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 43))).mpr hle

/-- E₁(b₃(43)) ≤ 0.021：E₁ ≤ e^{−b}/b ≤ e^{−2.86}/2.86（e^{−2.86} = e^{−1}·e^{−1}·e^{−0.86}）。 -/
theorem E1_b3_43_le : LPrime.E1 (bn43 3) ≤ (0.021 : ℝ) := by
  have hb3pos : 0 < bn43 3 := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2.86) b3_43_ge_286
  have hE : LPrime.E1 (bn43 3) ≤ Real.exp (-bn43 3) / bn43 3 := LPrime.E1_le (bn43 3) hb3pos
  have he286 : Real.exp (-(2.86 : ℝ)) ≤ (0.0579 : ℝ) := by
    have hsplit : -(2.86 : ℝ) = -1 + (-1) + (-(0.86 : ℝ)) := by norm_num
    rw [hsplit]
    rw [Real.exp_add]
    rw [Real.exp_add]
    have h1 : Real.exp (-1) * Real.exp (-(0.86 : ℝ)) ≤ (0.36790 : ℝ) * (0.4235 : ℝ) := by
      have h1a : Real.exp (-1) * Real.exp (-(0.86 : ℝ)) ≤ (0.36790 : ℝ) * Real.exp (-(0.86 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right LPrime.exp_neg_one_le (by positivity)
      have h1b : (0.36790 : ℝ) * Real.exp (-(0.86 : ℝ)) ≤ (0.36790 : ℝ) * (0.4235 : ℝ) := by
        exact mul_le_mul_of_nonneg_left exp_neg_086_le (by norm_num : (0 : ℝ) ≤ 0.36790)
      exact le_trans h1a h1b
    have h2 : Real.exp (-1) * (Real.exp (-1) * Real.exp (-(0.86 : ℝ))) ≤
        (0.36790 : ℝ) * ((0.36790 : ℝ) * (0.4235 : ℝ)) := by
      exact mul_le_mul LPrime.exp_neg_one_le h1 (by positivity) (by positivity)
    have hval : (0.36790 : ℝ) * ((0.36790 : ℝ) * (0.4235 : ℝ)) ≤ (0.0579 : ℝ) := by
      norm_num
    simpa [mul_assoc] using (le_trans h2 hval)
  have hmono : Real.exp (-bn43 3) ≤ Real.exp (-(2.86 : ℝ)) := by
    exact Real.exp_le_exp_of_le (by linarith [b3_43_ge_286])
  have hdiv : Real.exp (-(2.86 : ℝ)) / bn43 3 ≤ Real.exp (-(2.86 : ℝ)) / (2.86 : ℝ) := by
    have hb : bn43 3 ≥ (2.86 : ℝ) := b3_43_ge_286
    have hpos : (0 : ℝ) < 2.86 := by norm_num
    have hinv : (bn43 3)⁻¹ ≤ (2.86 : ℝ)⁻¹ := by
      simpa [one_div] using (one_div_le_one_div_of_le hpos hb)
    exact mul_le_mul_of_nonneg_left hinv (le_of_lt (Real.exp_pos (-(2.86 : ℝ))))
  have hfinal : Real.exp (-(2.86 : ℝ)) / (2.86 : ℝ) ≤ (0.021 : ℝ) := by
    have htop : Real.exp (-(2.86 : ℝ)) ≤ (0.0579 : ℝ) := he286
    have hbot : (0.0579 : ℝ) / (2.86 : ℝ) ≤ (0.021 : ℝ) := by norm_num
    exact (div_le_div_of_nonneg_right htop (by norm_num : (0 : ℝ) ≤ 2.86)).trans hbot
  calc
    LPrime.E1 (bn43 3) ≤ Real.exp (-bn43 3) / bn43 3 := hE
    _ ≤ Real.exp (-(2.86 : ℝ)) / bn43 3 := by
      exact div_le_div_of_nonneg_right hmono (le_of_lt hb3pos)
    _ ≤ Real.exp (-(2.86 : ℝ)) / (2.86 : ℝ) := hdiv
    _ ≤ (0.021 : ℝ) := hfinal

/-! ## 5. lprime1_43 绝对收敛（几何级数闭合） -/

/-- lprime1_43 级数绝对收敛：逐项界 |aₙ₊₁/(n+1)·E₁(bₙ₊₁)| ≤ (2/0.95)·e^{−0.95(n+1)}，
    右侧为几何级数 ⟹ Summable。 -/
theorem lprime1_43_summable :
    Summable (fun n : ℕ => (aE43 (n + 1) : ℝ) / (n + 1) * LPrime.E1 (bn43 (n + 1))) := by
  let q : ℝ := Real.exp (-(0.95 : ℝ))
  have hq_abs : |q| < 1 := by
    dsimp [q]
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_lt_one_iff.mpr (by norm_num : -(0.95 : ℝ) < 0))
  have hgeom : Summable (fun n : ℕ => (2 / (0.95 : ℝ)) * q ^ (n + 1)) := by
    have hs : Summable (fun n : ℕ => q ^ (n + 1)) := by
      simpa [pow_succ, mul_comm] using (summable_geometric_of_norm_lt_one hq_abs).mul_left q
    exact Summable.mul_left (2 / (0.95 : ℝ)) hs
  refine Summable.of_norm_bounded hgeom ?_
  intro n
  have hb : bn43 (n + 1) ≥ ((n : ℝ) + 1) * 0.95 := by
    simpa [Nat.cast_add, Nat.cast_one, mul_comm] using bn43_ge_095m (n + 1)
  have hbpos : 0 < bn43 (n + 1) := lt_of_lt_of_le (by positivity : 0 < ((n : ℝ) + 1) * 0.95) hb
  have hE1 : LPrime.E1 (bn43 (n + 1)) ≤ Real.exp (-bn43 (n + 1)) / bn43 (n + 1) :=
    LPrime.E1_le (bn43 (n + 1)) hbpos
  have hdiv : |(aE43 (n + 1) : ℝ) / (n + 1)| ≤ 2 := by
    rw [abs_div]
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) := by positivity
    rw [abs_of_nonneg hnn]
    have hc : |(aE43 (n + 1) : ℝ)| ≤ 2 * (((n : ℝ) + 1)) := by
      have hz : |(aE43 (n + 1) : ℤ)| ≤ 2 * (n + 1 : ℕ) := aE43_bound_all (n + 1)
      exact_mod_cast hz
    calc
      |(aE43 (n + 1) : ℝ)| / ((n : ℝ) + 1) ≤ (2 * (((n : ℝ) + 1))) / ((n : ℝ) + 1) := by
        exact div_le_div_of_nonneg_right hc hnn
      _ = 2 := by
        have hnz : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp [hnz]
  have hmono : Real.exp (-bn43 (n + 1)) ≤ q ^ (n + 1) := by
    have hneg : -bn43 (n + 1) ≤ -(0.95 : ℝ) * ((n : ℝ) + 1) := by linarith
    have h1 : Real.exp (-(0.95 : ℝ) * ((n : ℝ) + 1)) = q ^ (n + 1) := by
      dsimp [q]
      have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_one]
      rw [hcast]
      rw [mul_comm]
      rw [Real.exp_nat_mul]
    rw [← h1]
    exact Real.exp_le_exp_of_le hneg
  have hinv : (bn43 (n + 1))⁻¹ ≤ (((n : ℝ) + 1) * 0.95)⁻¹ := by
    have hpos : 0 < ((n : ℝ) + 1) * 0.95 := by positivity
    simpa [one_div] using (one_div_le_one_div_of_le hpos hb)
  have hE1b : LPrime.E1 (bn43 (n + 1)) ≤ q ^ (n + 1) / (((n : ℝ) + 1) * 0.95) := by
    have hstep1 : Real.exp (-bn43 (n + 1)) / bn43 (n + 1) ≤ q ^ (n + 1) / bn43 (n + 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hmono (inv_nonneg.mpr (le_of_lt hbpos))
    have hstep2 : q ^ (n + 1) / bn43 (n + 1) ≤ q ^ (n + 1) / (((n : ℝ) + 1) * 0.95) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ q ^ (n + 1))
    exact le_trans (le_trans hE1 hstep1) hstep2
  calc
    |(aE43 (n + 1) : ℝ) / (n + 1) * LPrime.E1 (bn43 (n + 1))|
        ≤ |(aE43 (n + 1) : ℝ) / (n + 1)| * LPrime.E1 (bn43 (n + 1)) := by
      rw [abs_mul]
      rw [abs_of_nonneg (LPrime.E1_nonneg (bn43 (n + 1)) hbpos)]
    _ ≤ 2 * LPrime.E1 (bn43 (n + 1)) := by
      exact mul_le_mul_of_nonneg_right hdiv (LPrime.E1_nonneg (bn43 (n + 1)) hbpos)
    _ ≤ 2 * (q ^ (n + 1) / (((n : ℝ) + 1) * 0.95)) := by
      exact mul_le_mul_of_nonneg_left hE1b (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ (2 / (0.95 : ℝ)) * q ^ (n + 1) := by
      have hnn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      have hle : (1 / (((n : ℝ) + 1) * 0.95) : ℝ) ≤ (1 / (0.95 : ℝ)) := by
        have hpos1 : (0 : ℝ) < ((n : ℝ) + 1) * 0.95 := by positivity
        have hpos2 : (0 : ℝ) < 0.95 := by norm_num
        have hmul : (0.95 : ℝ) ≤ ((n : ℝ) + 1) * 0.95 := by
          simpa using (mul_le_mul_of_nonneg_right hnn1 (by norm_num : (0 : ℝ) ≤ 0.95))
        exact (one_div_le_one_div_of_le hpos2 hmul)
      have hq : 0 ≤ q ^ (n + 1) := by positivity
      calc
        2 * (q ^ (n + 1) / (((n : ℝ) + 1) * 0.95)) = (2 / (0.95 : ℝ)) * q ^ (n + 1) * ((0.95 : ℝ) / (((n : ℝ) + 1) * 0.95)) := by
          ring
        _ ≤ (2 / (0.95 : ℝ)) * q ^ (n + 1) := by
          have hq2 : 0 ≤ (2 / (0.95 : ℝ)) * q ^ (n + 1) := by positivity
          have hle' : ((0.95 : ℝ) / (((n : ℝ) + 1) * 0.95)) ≤ 1 := by
            have hnn1' : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
              exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
            rw [div_eq_mul_inv]
            have hmul : (1 * 0.95 : ℝ) ≤ ((n : ℝ) + 1) * 0.95 := by
              exact mul_le_mul_of_nonneg_right hnn1' (by norm_num : (0 : ℝ) ≤ 0.95)
            have hinv' : (1 / (((n : ℝ) + 1) * 0.95) : ℝ) ≤ (1 / (1 * 0.95) : ℝ) := by
              have hp1 : (0 : ℝ) < ((n : ℝ) + 1) * 0.95 := by positivity
              have hp2 : (0 : ℝ) < 1 * 0.95 := by norm_num
              exact one_div_le_one_div_of_le hp2 hmul
            calc
              (0.95 : ℝ) / (((n : ℝ) + 1) * 0.95) = (0.95 : ℝ) * (1 / (((n : ℝ) + 1) * 0.95)) := by ring
              _ ≤ (0.95 : ℝ) * (1 / (1 * 0.95) : ℝ) := by
                exact mul_le_mul_of_nonneg_left hinv' (by norm_num : (0 : ℝ) ≤ 0.95)
              _ = 1 := by norm_num
          simpa using (mul_le_mul_of_nonneg_left hle' hq2)
        _ = (2 / (0.95 : ℝ)) * q ^ (n + 1) := by ring

/-! ## 6. 部分和前三项 + 尾界 ⟹ lprime1_43 > 0 -/

/-- 部分和前三项：Σ_{i<3} g i = E₁(b₁) − E₁(b₂) − (2/3)·E₁(b₃)
    （a₁ = 1, a₂ = −2, a₃ = −2）。 -/
lemma part3_43_eq :
    (∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (i + 1) * LPrime.E1 (bn43 (i + 1))) =
      LPrime.E1 (bn43 1) - LPrime.E1 (bn43 2) - (2 / 3 : ℝ) * LPrime.E1 (bn43 3) := by
  have ha1 : aE43 1 = 1 := by native_decide
  have ha2 : aE43 2 = -2 := by native_decide
  have ha3 : aE43 3 = -2 := by native_decide
  have h0 : (aE43 (0 + 1) : ℝ) / (0 + 1) * LPrime.E1 (bn43 (0 + 1)) = LPrime.E1 (bn43 1) := by
    rw [ha1]
    norm_num
  have h1 : (aE43 (1 + 1) : ℝ) / (1 + 1) * LPrime.E1 (bn43 (1 + 1)) = -LPrime.E1 (bn43 2) := by
    rw [ha2]
    norm_num
  have h2 : (aE43 (2 + 1) : ℝ) / (2 + 1) * LPrime.E1 (bn43 (2 + 1)) =
      -(2 / 3 : ℝ) * LPrime.E1 (bn43 3) := by
    rw [ha3]
    norm_num
  rw [show (∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (i + 1) * LPrime.E1 (bn43 (i + 1))) =
      (aE43 (0 + 1) : ℝ) / (0 + 1) * LPrime.E1 (bn43 (0 + 1)) +
      (aE43 (1 + 1) : ℝ) / (1 + 1) * LPrime.E1 (bn43 (1 + 1)) +
      (aE43 (2 + 1) : ℝ) / (2 + 1) * LPrime.E1 (bn43 (2 + 1)) by
    norm_num [Finset.sum_range_succ]]
  rw [h0, h1, h2]
  ring

/-- 部分和下界：Σ_{i<3} g i ≥ 0.0417（= 0.1337 − 0.078 − (2/3)·0.021）。 -/
lemma part3_43_lower : (0.0417 : ℝ) ≤
    (∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (i + 1) * LPrime.E1 (bn43 (i + 1))) := by
  rw [part3_43_eq]
  linarith [E1_b1_43_ge, E1_b2_43_le, E1_b3_43_le]

/-- 拆分：lprime1_43 = 2·(部分和 Σ_{i<3} + 尾项 Σ' g(n+3))。 -/
lemma lprime1_43_split :
    lprime1_43 = 2 * ((∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (i + 1) * LPrime.E1 (bn43 (i + 1))) +
      ∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))) := by
  unfold lprime1_43
  congr 1
  have htail : Summable (fun n : ℕ => (aE43 (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 3 + 1))) := by
    exact (summable_nat_add_iff 3).mpr lprime1_43_summable
  have hs : HasSum (fun n : ℕ => (aE43 (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 3 + 1)))
      (∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 3 + 1))) := htail.hasSum
  have hfull : HasSum (fun n : ℕ => (aE43 (n + 1) : ℝ) / (((n : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 1)))
      ((∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 3 + 1))) +
       ∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (((i : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (i + 1))) := by
    exact (hasSum_nat_add_iff (k := 3)
      (f := fun n : ℕ => (aE43 (n + 1) : ℝ) / (((n : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 1)))
      (g := (∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (((n + 3 : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 3 + 1))))).mp hs
  rw [show (∑' n : ℕ, (aE43 (n + 1) : ℝ) / (n + 1) * LPrime.E1 (bn43 (n + 1))) =
           (∑' n : ℕ, (aE43 (n + 1) : ℝ) / (((n : ℕ) : ℝ) + 1) * LPrime.E1 (bn43 (n + 1))) by
    apply tsum_congr
    intro n
    simp [Nat.cast_add]]
  rw [hfull.tsum_eq]
  simp [Nat.cast_add]
  ring

/-- 尾项逐项界：|aE43(m)/m·E₁(bₙ(m))| ≤ 2·e^{−0.95·m}/(4·0.95)，m ≥ 4。 -/
lemma g_abs_bound_43 (m : ℕ) (hm4 : 4 ≤ m) :
    |(aE43 m : ℝ) / m * LPrime.E1 (bn43 m)| ≤ 2 * Real.exp (-(0.95 : ℝ) * m) / (4 * (0.95 : ℝ)) := by
  have hbpos : 0 < bn43 m := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4 * 0.95) (bn43_ge_4c m hm4)
  have hdiv : |(aE43 m : ℝ) / m| ≤ 2 := by
    rw [abs_div]
    have hmcast : (0 : ℝ) ≤ (m : ℝ) := by positivity
    rw [abs_of_nonneg hmcast]
    have hc : |(aE43 m : ℝ)| ≤ 2 * (m : ℝ) := by
      have hz : |(aE43 m : ℤ)| ≤ 2 * (m : ℤ) := aE43_bound_all m
      exact_mod_cast hz
    calc
      |(aE43 m : ℝ)| / (m : ℝ) ≤ (2 * (m : ℝ)) / (m : ℝ) := by
        exact div_le_div_of_nonneg_right hc hmcast
      _ = 2 := by
        have hmz : (m : ℝ) ≠ 0 := by positivity
        field_simp [hmz]
  have hE0 : 0 ≤ LPrime.E1 (bn43 m) := LPrime.E1_nonneg (bn43 m) hbpos
  have hg2E : |(aE43 m : ℝ) / m * LPrime.E1 (bn43 m)| ≤ 2 * LPrime.E1 (bn43 m) := by
    rw [abs_mul]
    rw [abs_of_nonneg hE0]
    exact mul_le_mul_of_nonneg_right hdiv hE0
  have hmono : Real.exp (-bn43 m) ≤ Real.exp (-(0.95 : ℝ) * m) := by
    have hb : (m : ℝ) * 0.95 ≤ bn43 m := bn43_ge_095m m
    have hneg : -bn43 m ≤ -(0.95 : ℝ) * m := by linarith
    exact (Real.exp_le_exp).mpr hneg
  have hinv : (bn43 m)⁻¹ ≤ (4 * (0.95 : ℝ))⁻¹ := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 * 0.95) (bn43_ge_4c m hm4))
  have hE1 : LPrime.E1 (bn43 m) ≤ Real.exp (-bn43 m) / bn43 m := LPrime.E1_le (bn43 m) hbpos
  have hE2 : LPrime.E1 (bn43 m) ≤ Real.exp (-(0.95 : ℝ) * m) / (4 * (0.95 : ℝ)) := by
    have hstep1 : Real.exp (-bn43 m) / bn43 m ≤ Real.exp (-(0.95 : ℝ) * m) / bn43 m := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hmono (inv_nonneg.mpr (le_of_lt hbpos))
    have hstep2 : Real.exp (-(0.95 : ℝ) * m) / bn43 m ≤
        Real.exp (-(0.95 : ℝ) * m) / (4 * (0.95 : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (le_of_lt (Real.exp_pos (-(0.95 : ℝ) * m)))
    exact le_trans (le_trans hE1 hstep1) hstep2
  calc
    |(aE43 m : ℝ) / m * LPrime.E1 (bn43 m)| ≤ 2 * LPrime.E1 (bn43 m) := hg2E
    _ ≤ 2 * (Real.exp (-(0.95 : ℝ) * m) / (4 * (0.95 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hE2 (by norm_num : (0 : ℝ) ≤ 2)
    _ = 2 * Real.exp (-(0.95 : ℝ) * m) / (4 * (0.95 : ℝ)) := by ring

/-- 尾项绝对值界：|Σ'_{m ≥ 4}| ≤ 0.0215（几何级数闭合）。 -/
theorem tail_abs_43_le :
    |∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))| ≤
      (0.0215 : ℝ) := by
  have hsum : Summable (fun n : ℕ => (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using (summable_nat_add_iff 3).mpr lprime1_43_summable
  have hbound : ∀ n : ℕ,
      |(aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))| ≤
        (2 / (4 * (0.95 : ℝ))) * Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ)) := by
    intro n
    have hb4 : 4 ≤ n + 4 := by omega
    have hg' := g_abs_bound_43 (n + 4) hb4
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hg'
  have hsum4 : Summable (fun n : ℕ => (aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))) := by
    have h1 : (fun n : ℕ => (aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))) =
        (fun n : ℕ => (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))) := by
      funext n
      have hc : n + 3 + 1 = n + 4 := by omega
      rw [hc]
      congr 1
      ring_nf
    rw [h1]
    exact hsum
  have hf_abs_sum : Summable (fun n : ℕ => |(aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))|) := by
    exact hsum4.norm
  have hq : ‖Real.exp (-(0.95 : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_lt_one_iff.mpr (by norm_num : -(0.95 : ℝ) < 0))
  have hb := hasSum_geometric_of_norm_lt_one hq
  have hg0 : HasSum (fun n : ℕ => (Real.exp (-(0.95 : ℝ))) ^ 4 * (Real.exp (-(0.95 : ℝ))) ^ n)
      ((Real.exp (-(0.95 : ℝ))) ^ 4 * (1 - Real.exp (-(0.95 : ℝ)))⁻¹) := by
    exact hb.mul_left ((Real.exp (-(0.95 : ℝ))) ^ 4)
  have hp : ∀ n : ℕ, (Real.exp (-(0.95 : ℝ))) ^ 4 * (Real.exp (-(0.95 : ℝ))) ^ n =
      Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ)) := by
    intro n
    rw [← pow_add]
    have hswap : 4 + n = n + 4 := by omega
    rw [hswap]
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  have hg' : HasSum (fun n : ℕ => Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ)))
      ((Real.exp (-(0.95 : ℝ))) ^ 4 * (1 - Real.exp (-(0.95 : ℝ)))⁻¹) := by
    exact hg0.congr_fun (fun n : ℕ => (hp n).symm)
  have hg : HasSum (fun n : ℕ => Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ)))
      ((Real.exp (-(0.95 : ℝ))) ^ 4 / (1 - Real.exp (-(0.95 : ℝ)))) := by
    simpa [div_eq_mul_inv] using hg'
  have hgs2 : Summable (fun n : ℕ => (2 / (4 * (0.95 : ℝ))) * Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ))) := by
    exact hg.summable.mul_left (2 / (4 * (0.95 : ℝ)))
  have hsum_le : (∑' n : ℕ, |(aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))|) ≤
      ∑' n : ℕ, (2 / (4 * (0.95 : ℝ))) * Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ)) := by
    exact hf_abs_sum.tsum_le_tsum hbound hgs2
  have habs : |∑' n : ℕ, (aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))| ≤
      ∑' n : ℕ, |(aE43 (n + 4) : ℝ)| / |(n + 4 : ℝ)| * |LPrime.E1 (bn43 (n + 4))| := by
    have hnorm : Summable (fun n : ℕ => ‖(aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))‖) := by
      convert hf_abs_sum using 1
      ext n
      rw [Real.norm_eq_abs]
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  have g_sum_abs43 : (∑' n : ℕ, |(aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))|) =
      (∑' n : ℕ, |(aE43 (n + 4) : ℝ)| / |(n + 4 : ℝ)| * |LPrime.E1 (bn43 (n + 4))|) := by
    apply tsum_congr
    intro n
    rw [abs_mul]
    rw [abs_div]
  have hval4 : (∑' n : ℕ, (2 / (4 * (0.95 : ℝ))) * Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ))) ≤
      (0.0215 : ℝ) := by
    have hq4 : (Real.exp (-(0.95 : ℝ))) ^ 4 ≤ (0.3869 : ℝ) ^ 4 := by
      exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) exp_neg_095_le 4
    have hden : 1 - (0.3869 : ℝ) ≤ 1 - Real.exp (-(0.95 : ℝ)) := by
      linarith [exp_neg_095_le]
    calc
      (∑' n : ℕ, (2 / (4 * (0.95 : ℝ))) * Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ)))
          = (2 / (4 * (0.95 : ℝ))) * (∑' n : ℕ, Real.exp (-(0.95 : ℝ) * (n + 4 : ℕ))) := by
        rw [tsum_mul_left]
      _ = (2 / (4 * (0.95 : ℝ))) * ((Real.exp (-(0.95 : ℝ))) ^ 4 / (1 - Real.exp (-(0.95 : ℝ)))) := by
        rw [hg.tsum_eq]
      _ ≤ (2 / (4 * (0.95 : ℝ))) * ((0.3869 : ℝ) ^ 4 / (1 - Real.exp (-(0.95 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hq4 (by linarith : 0 ≤ 1 - Real.exp (-(0.95 : ℝ)))) (by norm_num)
      _ ≤ (2 / (4 * (0.95 : ℝ))) * ((0.3869 : ℝ) ^ 4 / (1 - (0.3869 : ℝ))) := by
        have hq4n : (0 : ℝ) ≤ (0.3869 : ℝ) ^ 4 := by positivity
        have hinv2 : 1 / (1 - Real.exp (-(0.95 : ℝ))) ≤ 1 / (1 - (0.3869 : ℝ)) := by
          exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 - 0.3869) hden
        have hm : (1 / (1 - Real.exp (-(0.95 : ℝ)))) * (0.3869 : ℝ) ^ 4 ≤
            (1 / (1 - (0.3869 : ℝ))) * (0.3869 : ℝ) ^ 4 := by
          exact mul_le_mul_of_nonneg_right hinv2 hq4n
        have hquot : (0.3869 : ℝ) ^ 4 / (1 - Real.exp (-(0.95 : ℝ))) ≤
            (0.3869 : ℝ) ^ 4 / (1 - (0.3869 : ℝ)) := by
          simpa [div_eq_mul_inv, mul_comm] using hm
        exact mul_le_mul_of_nonneg_left hquot (by norm_num : (0 : ℝ) ≤ 2 / (4 * 0.95))
      _ ≤ (0.0215 : ℝ) := by norm_num
  have htmp2 : |∑' n : ℕ, (aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))| ≤ (0.0215 : ℝ) := by
    have htmp2a : |∑' n : ℕ, (aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))| ≤
        ∑' n : ℕ, |(aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))| := by
      rw [g_sum_abs43]
      exact habs
    exact le_trans (le_trans htmp2a hsum_le) hval4
  have hshift : (∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))) =
      (∑' n : ℕ, (aE43 (n + 4) : ℝ) / (n + 4) * LPrime.E1 (bn43 (n + 4))) := by
    apply tsum_congr
    intro n
    congr 2
    ring_nf
  rw [hshift]
  exact htmp2

/-- 尾项总界（无绝对值）：Σ'_{m ≥ 4} ≤ 0.0215。 -/
theorem tail_43_le : (∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))) ≤
    (0.0215 : ℝ) := by
  exact le_trans (le_abs_self (∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1)))) tail_abs_43_le

/-- **L′(43a1,1) > 0（真定理）**：部分和前三项 ≥ 0.0417 > 尾 ≤ 0.0215。 -/
theorem lprime1_43_pos : 0 < lprime1_43 := by
  have hsplit := lprime1_43_split
  rw [hsplit]
  have hpart : (0 : ℝ) ≤ (∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (i + 1) * LPrime.E1 (bn43 (i + 1))) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 0.0417) part3_43_lower
  have htail := tail_43_le
  have hpos : (0 : ℝ) <
      (∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (i + 1) * LPrime.E1 (bn43 (i + 1))) +
        ∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1)) := by
    have hpart_gt : (0.0417 : ℝ) ≤ (∑ i ∈ Finset.range 3, (aE43 (i + 1) : ℝ) / (i + 1) * LPrime.E1 (bn43 (i + 1))) :=
      part3_43_lower
    have htail_le : (∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))) ≤ (0.0215 : ℝ) :=
      tail_43_le
    have htail_lb : -(0.0215 : ℝ) ≤ (∑' n : ℕ, (aE43 (n + 3 + 1) : ℝ) / (n + 3 + 1) * LPrime.E1 (bn43 (n + 3 + 1))) := by
      exact le_trans (neg_le_neg tail_abs_43_le) (neg_abs_le _)
    linarith
  exact mul_pos (by norm_num : (0 : ℝ) < 2) hpos

end

end BSD.LPrime43
