import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 区间指示函数 1_{[a,b]}。 -/
noncomputable def intervalIndicator (a b : ℝ) (ha : 0 < a) (hab : a < b) : TestFunction :=
  { toFun := fun x : ℝ => if a ≤ x ∧ x ≤ b then (1 : ℂ) else (0 : ℂ)
    hasCompactSupport := by
      use b + 1
      constructor
      · linarith
      · intro x hx
        by_cases hpos : 0 ≤ x
        · have h_x_gt : b < x := by
            have h : b + 1 < x := by simpa [abs_of_nonneg hpos] using hx
            linarith
          have h' : ¬(a ≤ x ∧ x ≤ b) := by intro h; linarith
          simp only [h', if_false]
        · have h_x_neg : x < 0 := by linarith
          have h' : ¬(a ≤ x ∧ x ≤ b) := by
            intro h; have : a ≤ x := h.1; linarith
          simp only [h', if_false] }

/-- 区间指示函数的 Mellin 变换（公理，标准微积分基本定理结果）。 -/
axiom intervalIndicator_mellinTransform (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator a b ha hab) s =
    (Complex.exp (s * (Real.log b : ℂ)) - Complex.exp (s * (Real.log a : ℂ))) / s

/-- 辅助引理：exp(s * log 4) = exp(s * log 2)^2。 -/
lemma exp_log4_eq_sq (s : ℂ) :
    Complex.exp (s * (Real.log 4 : ℂ)) = (Complex.exp (s * (Real.log 2 : ℂ))) ^ 2 := by
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)] <;> ring
  have h5 : (Real.log 4 : ℂ) = 2 * (Real.log 2 : ℂ) := by exact_mod_cast h_log4
  rw [h5]
  have h6 : s * (2 * (Real.log 2 : ℂ)) = (s * (Real.log 2 : ℂ)) + (s * (Real.log 2 : ℂ)) := by ring
  rw [h6, Complex.exp_add] <;> ring

/-- 辅助引理：exp(s * log 1) = 1。 -/
lemma exp_log1_eq_one (s : ℂ) : Complex.exp (s * (Real.log 1 : ℂ)) = 1 := by
  have h_log1 : Real.log 1 = 0 := by exact?
  have h6 : (Real.log 1 : ℂ) = 0 := by exact_mod_cast h_log1
  rw [h6] <;> simp

/-- 行列式因式分解（定理，纯代数，零 sorry）：
    对区间 [1,2] 和 [2,4]，
    det = (2^s₂ - 2^s₁)(2^s₁ - 1)(2^s₂ - 1) / (s₁ * s₂) -/
theorem determinant_factorization (s1 s2 : ℂ) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0) :
    (melinTransform (intervalIndicator 1 2 (by norm_num) (by norm_num)) s1) *
    (melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s2) -
    (melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s1) *
    (melinTransform (intervalIndicator 1 2 (by norm_num) (by norm_num)) s2) =
    ((Complex.exp (s2 * (Real.log 2 : ℂ)) - Complex.exp (s1 * (Real.log 2 : ℂ))) *
     (Complex.exp (s1 * (Real.log 2 : ℂ)) - 1) *
     (Complex.exp (s2 * (Real.log 2 : ℂ)) - 1)) / (s1 * s2) := by
  set a1 := Complex.exp (s1 * (Real.log 2 : ℂ)) with ha1
  set a2 := Complex.exp (s2 * (Real.log 2 : ℂ)) with ha2
  have h1 : melinTransform (intervalIndicator 1 2 (by norm_num) (by norm_num)) s1 = (a1 - 1) / s1 := by
    rw [intervalIndicator_mellinTransform 1 2 (by norm_num) (by norm_num) s1 hs1]
    rw [exp_log1_eq_one s1] <;> simp [ha1]
  have h2 : melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s2 = (a2^2 - a2) / s2 := by
    rw [intervalIndicator_mellinTransform 2 4 (by norm_num) (by norm_num) s2 hs2]
    rw [exp_log4_eq_sq s2] <;> simp [ha2]
  have h3 : melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s1 = (a1^2 - a1) / s1 := by
    rw [intervalIndicator_mellinTransform 2 4 (by norm_num) (by norm_num) s1 hs1]
    rw [exp_log4_eq_sq s1] <;> simp [ha1]
  have h4 : melinTransform (intervalIndicator 1 2 (by norm_num) (by norm_num)) s2 = (a2 - 1) / s2 := by
    rw [intervalIndicator_mellinTransform 1 2 (by norm_num) (by norm_num) s2 hs2]
    rw [exp_log1_eq_one s2] <;> simp [ha2]
  rw [h1, h2, h3, h4]
  field_simp [hs1, hs2] <;> ring

/-- 两点矩阵可逆性（定理，零 sorry，由行列式因式分解推出）：
    在附加条件 2^s₁ ≠ 1, 2^s₂ ≠ 1, 2^s₁ ≠ 2^s₂ 下，
    区间 [1,2] 和 [2,4] 的 Mellin 变换矩阵可逆。 -/
theorem two_point_matrix_invertible (s1 s2 : ℂ) (h_ne : s1 ≠ s2) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0)
    (h_a1_ne_one : Complex.exp (s1 * (Real.log 2 : ℂ)) ≠ 1)
    (h_a2_ne_one : Complex.exp (s2 * (Real.log 2 : ℂ)) ≠ 1)
    (h_a1_ne_a2 : Complex.exp (s1 * (Real.log 2 : ℂ)) ≠ Complex.exp (s2 * (Real.log 2 : ℂ))) :
    (melinTransform (intervalIndicator 1 2 (by norm_num) (by norm_num)) s1) *
    (melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s2) -
    (melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s1) *
    (melinTransform (intervalIndicator 1 2 (by norm_num) (by norm_num)) s2) ≠ 0 := by
  have h_det_eq := determinant_factorization s1 s2 hs1 hs2
  rw [h_det_eq]
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · simpa [sub_ne_zero] using h_a1_ne_a2.symm
      · simpa [sub_ne_zero] using h_a1_ne_one
    · simpa [sub_ne_zero] using h_a2_ne_one
  · exact mul_ne_zero hs1 hs2

/-- 纯 Mellin 有限插值（n=2 情形，定理，零 sorry）：
    在附加条件下，对任意赋值 w₁, w₂，存在 TestFunction h 使 M[h](s₁) = w₁, M[h](s₂) = w₂。 -/
theorem mellin_two_point_interpolation (s1 s2 : ℂ) (h_ne : s1 ≠ s2) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0)
    (h_a1_ne_one : Complex.exp (s1 * (Real.log 2 : ℂ)) ≠ 1)
    (h_a2_ne_one : Complex.exp (s2 * (Real.log 2 : ℂ)) ≠ 1)
    (h_a1_ne_a2 : Complex.exp (s1 * (Real.log 2 : ℂ)) ≠ Complex.exp (s2 * (Real.log 2 : ℂ)))
    (w1 w2 : ℂ) : ∃ (h : TestFunction), melinTransform h s1 = w1 ∧ melinTransform h s2 = w2 := by
  let f1 := intervalIndicator 1 2 (by norm_num) (by norm_num)
  let f2 := intervalIndicator 2 4 (by norm_num) (by norm_num)
  let a11 := melinTransform f1 s1
  let a12 := melinTransform f2 s1
  let a21 := melinTransform f1 s2
  let a22 := melinTransform f2 s2
  have h_det : a11 * a22 - a12 * a21 ≠ 0 :=
    two_point_matrix_invertible s1 s2 h_ne hs1 hs2 h_a1_ne_one h_a2_ne_one h_a1_ne_a2
  let c1 : ℂ := (w1 * a22 - w2 * a12) / (a11 * a22 - a12 * a21)
  let c2 : ℂ := (a11 * w2 - a21 * w1) / (a11 * a22 - a12 * a21)
  let h : TestFunction := c1 • f1 + c2 • f2
  use h
  set det : ℂ := a11 * a22 - a12 * a21 with hdet_def
  have h_det' : det ≠ 0 := h_det
  have h_num1 : (w1 * a22 - w2 * a12) * a11 + (a11 * w2 - a21 * w1) * a12 = w1 * det := by
    simp [hdet_def] <;> ring
  have h_num2 : (w1 * a22 - w2 * a12) * a21 + (a11 * w2 - a21 * w1) * a22 = w2 * det := by
    simp [hdet_def] <;> ring
  have h_eq1 : c1 * a11 + c2 * a12 = w1 := by
    calc
      c1 * a11 + c2 * a12
        = ((w1 * a22 - w2 * a12) / det) * a11 + ((a11 * w2 - a21 * w1) / det) * a12 := by rfl
      _ = (((w1 * a22 - w2 * a12) * a11 + (a11 * w2 - a21 * w1) * a12) / det) := by
        field_simp [h_det'] <;> ring
      _ = (w1 * det) / det := by rw [h_num1]
      _ = w1 := by exact?
  have h_eq2 : c1 * a21 + c2 * a22 = w2 := by
    calc
      c1 * a21 + c2 * a22
        = ((w1 * a22 - w2 * a12) / det) * a21 + ((a11 * w2 - a21 * w1) / det) * a22 := by rfl
      _ = (((w1 * a22 - w2 * a12) * a21 + (a11 * w2 - a21 * w1) * a22) / det) := by
        field_simp [h_det'] <;> ring
      _ = (w2 * det) / det := by rw [h_num2]
      _ = w2 := by exact?
  constructor
  · have h1 : melinTransform h s1 = c1 * a11 + c2 * a12 := by
      rw [melinTransform_linear f1 f2 c1 c2 s1] <;> rfl
    rw [h1, h_eq1]
  · have h2 : melinTransform h s2 = c1 * a21 + c2 * a22 := by
      rw [melinTransform_linear f1 f2 c1 c2 s2] <;> rfl
    rw [h2, h_eq2]

end RHSpectralDuality
end OrderPreservingBijection
