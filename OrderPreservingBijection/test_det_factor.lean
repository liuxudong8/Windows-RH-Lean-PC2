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

/-- 行列式因式分解（定理，纯代数）：
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
    rw [exp_log1_eq_one s1]
    <;> simp [ha1]
  have h2 : melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s2 = (a2^2 - a2) / s2 := by
    rw [intervalIndicator_mellinTransform 2 4 (by norm_num) (by norm_num) s2 hs2]
    rw [exp_log4_eq_sq s2]
    <;> simp [ha2]
  have h3 : melinTransform (intervalIndicator 2 4 (by norm_num) (by norm_num)) s1 = (a1^2 - a1) / s1 := by
    rw [intervalIndicator_mellinTransform 2 4 (by norm_num) (by norm_num) s1 hs1]
    rw [exp_log4_eq_sq s1]
    <;> simp [ha1]
  have h4 : melinTransform (intervalIndicator 1 2 (by norm_num) (by norm_num)) s2 = (a2 - 1) / s2 := by
    rw [intervalIndicator_mellinTransform 1 2 (by norm_num) (by norm_num) s2 hs2]
    rw [exp_log1_eq_one s2]
    <;> simp [ha2]
  rw [h1, h2, h3, h4]
  field_simp [hs1, hs2] <;> ring

end RHSpectralDuality
end OrderPreservingBijection
