/-
  阶段1：双曲长度恒等式

  定理：对任意 t > 1，
    2 * arccosh ((sqrt t + 1 / sqrt t) / 2) = log t

  其中 arccosh x := log (x + sqrt (x^2 - 1)) （x ≥ 1）

  注：论文附录A写 t > 0，但 0 < t < 1 时 log t < 0 而左边非负，
  实际应用中 t = Nm(p) > 1（素理想范数），故定理假设为 1 < t。

  这是论文第4节和附录A的核心解析恒等式，
  连接双曲测地线长度公式与素理想范数的对数。
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

-- 反双曲余弦定义：arccosh x = log(x + sqrt(x^2 - 1))，要求 x ≥ 1
noncomputable def arccosh (x : ℝ) : ℝ := log (x + sqrt (x^2 - 1))

-- 引理：若 x ≥ 1，则 x + sqrt(x^2 - 1) > 0
lemma arccosh_arg_pos {x : ℝ} (hx : 1 ≤ x) : 0 < x + sqrt (x^2 - 1) := by
  have h1 : 0 < x := by linarith
  have h2 : 0 ≤ sqrt (x^2 - 1) := sqrt_nonneg _
  linarith

-- 引理：若 x ≥ 1，则 cosh (arccosh x) = x
lemma cosh_arccosh {x : ℝ} (hx : 1 ≤ x) :
    (exp (arccosh x) + exp (-(arccosh x))) / 2 = x := by
  set y := x + sqrt (x^2 - 1) with hy_def
  have hy_pos : 0 < y := arccosh_arg_pos hx
  have h1 : arccosh x = log y := by rfl
  have h2 : exp (arccosh x) = y := by
    rw [h1, exp_log hy_pos]
  have h3 : y * (x - sqrt (x^2 - 1)) = 1 := by
    have h4 : 0 ≤ x^2 - 1 := by nlinarith
    nlinarith [sq_sqrt h4]
  have h5 : x - sqrt (x^2 - 1) = 1 / y := by
    field_simp [hy_pos.ne'] <;> linarith
  have h6 : exp (-(arccosh x)) = 1 / y := by
    have h7 : exp (-(arccosh x)) = (exp (arccosh x))⁻¹ := by
      rw [exp_neg]
    rw [h7, h2]
    <;> field_simp
  rw [h2, h6]
  have h8 : y + 1 / y = 2 * x := by
    rw [hy_def]
    have h10 : 0 ≤ x^2 - 1 := by nlinarith
    field_simp [hy_pos.ne']
    <;> nlinarith [sq_sqrt h10]
  linarith

-- 引理：arccosh x ≥ 0 （x ≥ 1）
lemma arccosh_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ arccosh x := by
  have h1 : 1 ≤ x + sqrt (x^2 - 1) := by
    have h2 : 0 ≤ sqrt (x^2 - 1) := sqrt_nonneg _
    linarith
  have h3 : 0 ≤ log (x + sqrt (x^2 - 1)) := log_nonneg h1
  exact h3

-- 主定理：双曲长度恒等式
theorem hyperbolic_length_identity (t : ℝ) (ht : 1 < t) :
    2 * arccosh ((sqrt t + 1 / sqrt t) / 2) = log t := by
  have h_t_pos : 0 < t := by linarith
  have h_sqrt_pos : 0 < sqrt t := sqrt_pos.mpr h_t_pos
  have h_sqrt_gt_one : 1 < sqrt t := by
    have h : 1 < t := ht
    have h2 : (1 : ℝ) ^ 2 < t := by nlinarith
    exact lt_sqrt_of_sq_lt h2
  have h_inv_sqrt_lt_one : 1 / sqrt t < 1 := by
    have h : 1 < sqrt t := h_sqrt_gt_one
    have h2 : 0 < sqrt t := h_sqrt_pos
    have h3 : 1 / sqrt t < 1 := by
      apply (div_lt_one (by positivity)).mpr
      linarith
    exact h3
  set y := (sqrt t + 1 / sqrt t) / 2 with hy_def
  have hy_ge_one : 1 ≤ y := by
    have h1 : 0 < sqrt t := h_sqrt_pos
    have h2 : 0 < 1 / sqrt t := by positivity
    have h3 : sqrt t + 1 / sqrt t ≥ 2 := by
      have h4 : (sqrt t - 1 / sqrt t) ^ 2 ≥ 0 := by positivity
      have h5 : (sqrt t) * (1 / sqrt t) = 1 := by
        field_simp [h1.ne'] <;> ring
      nlinarith
    linarith
  set x := arccosh y with hx_def
  have h_x_nonneg : 0 ≤ x := arccosh_nonneg hy_ge_one
  have h_cosh_x : (exp x + exp (-x)) / 2 = y := cosh_arccosh hy_ge_one
  have h_exp_eq : exp x + exp (-x) = sqrt t + 1 / sqrt t := by
    linarith [h_cosh_x, hy_def]
  have h_quadratic : (exp x) ^ 2 - (sqrt t + 1 / sqrt t) * exp x + 1 = 0 := by
    have h_pos : 0 < exp x := exp_pos x
    have h : (exp x + exp (-x)) * exp x = (sqrt t + 1 / sqrt t) * exp x := by
      rw [h_exp_eq]
    have h2 : (exp x + exp (-x)) * exp x = (exp x) ^ 2 + 1 := by
      have h3 : exp (-x) * exp x = 1 := by
        calc
          exp (-x) * exp x = exp (-x + x) := by rw [← exp_add]
          _ = exp 0 := by ring_nf
          _ = 1 := by simp
      ring_nf at * <;> linarith
    linarith
  have h_factor : ((exp x) - sqrt t) * ((exp x) - 1 / sqrt t) = 0 := by
    have h4 : (exp x) ^ 2 - (sqrt t + 1 / sqrt t) * exp x + 1 =
        ((exp x) - sqrt t) * ((exp x) - 1 / sqrt t) := by
      field_simp [h_sqrt_pos.ne'] <;> ring
    rw [h4] at h_quadratic
    exact h_quadratic
  have h5 : (exp x) - sqrt t = 0 ∨ (exp x) - 1 / sqrt t = 0 :=
    eq_zero_or_eq_zero_of_mul_eq_zero h_factor
  have h_exp_sqrt : exp x = sqrt t := by
    cases h5 with
    | inl h5 =>
      linarith
    | inr h5 =>
      have h6 : exp x = 1 / sqrt t := by linarith
      have h7 : exp x < 1 := by
        rw [h6]
        exact h_inv_sqrt_lt_one
      have h8 : x < 0 := by
        have h9 : exp x < 1 := h7
        have h10 : exp 0 = (1 : ℝ) := by simp
        have h11 : exp x < exp 0 := by rw [h10] <;> exact h9
        have h12 : x < 0 := (exp_strictMono).lt_iff_lt.mp h11
        exact h12
      linarith [h_x_nonneg]
  have h_x_eq : x = log (sqrt t) := by
    have h1 : exp x = sqrt t := h_exp_sqrt
    have h2 : 0 < sqrt t := h_sqrt_pos
    have h3 : log (exp x) = log (sqrt t) := by rw [h1]
    have h4 : log (exp x) = x := log_exp x
    linarith
  have h_final : 2 * x = log t := by
    rw [h_x_eq]
    have h4 : log (sqrt t) = log t / 2 := log_sqrt (by linarith)
    rw [h4] <;> ring
  simpa [hx_def] using h_final
