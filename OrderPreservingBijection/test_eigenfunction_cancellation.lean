import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open Complex OrderPreservingBijection

-- 如果 f ≠ 0，那么存在某个 z 使得 f.toFun z ≠ 0
lemma l2function_ne_zero_exists {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M}
    (f : L2Function M μ) (h : f ≠ 0) : ∃ (z : M), f.toFun z ≠ 0 := by
  by_contra h'
  push_neg at h'
  have h_all_zero : ∀ (z : M), f.toFun z = 0 := h'
  have h_toFun_eq_zero : f.toFun = (0 : L2Function M μ).toFun := by
    funext z
    exact h_all_zero z
  have h_f_eq_zero : f = 0 := l2function_ext f (0 : L2Function M μ) h_toFun_eq_zero
  exact h h_f_eq_zero

-- 测试：eigenfunction_cancellation
theorem eigenfunction_cancellation_test (n : ℕ) (a b : ℂ) :
    a • threeManifoldEigenfunction n = b • threeManifoldEigenfunction n → a = b := by
  intro h
  have h_ne_zero : threeManifoldEigenfunction n ≠ 0 := threeManifoldEigenfunction_nonzero n
  have h_exists : ∃ (z : ManifoldM), (threeManifoldEigenfunction n).toFun z ≠ 0 :=
    l2function_ne_zero_exists (threeManifoldEigenfunction n) h_ne_zero
  rcases h_exists with ⟨z, hz⟩
  have h3 : (a • threeManifoldEigenfunction n).toFun z = (b • threeManifoldEigenfunction n).toFun z := by
    rw [h]
  have h4 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := by
    have h5 : (a • threeManifoldEigenfunction n).toFun z = a * (threeManifoldEigenfunction n).toFun z := by
      rfl
    have h6 : (b • threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := by
      rfl
    rw [h5, h6] at h3
    exact h3
  have h7 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := h4
  have h8 : a = b := by
    have h9 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := h7
    have h10 : a = b := by
      exact?
    exact h10
  exact h8

end RHSpectralDuality
