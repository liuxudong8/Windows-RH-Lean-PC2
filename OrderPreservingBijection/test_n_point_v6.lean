import OrderPreservingBijection.test_exists_n
import OrderPreservingBijection.test_mellin_pow4
import OrderPreservingBijection.test_finset_sum5

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助：a ≠ b → a - b ≠ 0（复数）。 -/
lemma complex_sub_ne_zero (a b : ℂ) (h : a ≠ b) : a - b ≠ 0 := by exact?

/-- n 点 Mellin 有限插值（定理）。 -/
theorem mellin_n_point_interpolation (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0) (w : Fin n → ℂ) :
    ∃ (h : TestFunction), ∀ i : Fin n, melinTransform h (s i) = w i := by
  rcases exists_base_for_finite_set n s h_inj h_ne_zero with ⟨a, ha_gt_one, h_a_ne_one, h_a_distinct⟩
  set v : Fin n → ℂ := fun j => Complex.exp (s j * (Real.log a : ℂ)) with hv_def
  set f : Fin n → TestFunction := fun i =>
    intervalIndicator (a ^ (i : ℕ)) (a ^ ((i : ℕ) + 1)) (by positivity) (pow_lt_pow_succ a ha_gt_one (i : ℕ)) with hf_def
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => melinTransform (f i) (s j)) with hA_def
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde v with hV_def
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j => (v j - 1) / (s j)) with hD_def
  have hv_ne_one : ∀ j, v j ≠ 1 := h_a_ne_one
  have hv_distinct : ∀ i j, i ≠ j → v i ≠ v j := h_a_distinct
  have h_matrix_eq : ∀ (i j : Fin n), A i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
    intro i j
    have h : melinTransform (f i) (s j) = (v j) ^ (i : ℕ) * (v j - 1) / (s j) :=
      mellin_interval_pow a ha_gt_one (i : ℕ) (s j) (h_ne_zero j)
    simpa [A] using h
  have hA_eq_VD : A = V * D := by
    ext i j
    have h1 : (V * D) i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
      have h_sum : (V * D) i j = ∑ k : Fin n, V i k * D k j := by rfl
      rw [h_sum]
      have h2 : ∑ k : Fin n, V i k * D k j = V i j * D j j := by
        rw [Finset.sum_eq_single j]
        · intro k _ hkj
          simp [D, Matrix.diagonal, hkj] <;> ring
        · simp
      rw [h2]
      have hVij : V i j = (v j) ^ (i : ℕ) := by simp [V, Matrix.vandermonde]
      have hDjj : D j j = (v j - 1) / (s j) := by simp [D, Matrix.diagonal]
      rw [hVij, hDjj] <;> ring
    have h2 : A i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := h_matrix_eq i j
    rw [h2, h1]
  have hV_det_ne_zero : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde v]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have h_j_gt_i : i < j := Finset.mem_Ioi.mp hj
    have h_ij : i ≠ j := by
      intro h_eq
      have h_cont : j < j := by rw [h_eq] at h_j_gt_i; exact h_j_gt_i
      exact lt_irrefl j h_cont
    have h_vi_ne_vj : v i ≠ v j := hv_distinct i j h_ij
    have h_vj_ne_vi : v j ≠ v i := Ne.symm h_vi_ne_vj
    have h : (v j - v i : ℂ) ≠ 0 := by
      exact?
    exact h
  have hD_det_ne_zero : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have h1 : v j - 1 ≠ 0 := by
      intro h
      exact hv_ne_one j (by rw [←sub_eq_zero]; exact h)
    have h3 : s j ≠ 0 := h_ne_zero j
    exact div_ne_zero h1 h3
  have hA_det_ne_zero : A.det ≠ 0 := by
    rw [hA_eq_VD, Matrix.det_mul]
    intro h
    by_cases hV : V.det = 0
    · exact hV_det_ne_zero hV
    · have hD : D.det = 0 := by
        field_simp [hV] at h
        <;> simpa using h
      exact hD_det_ne_zero hD
  have hA_det_isUnit : IsUnit A.det := by
    refine' IsUnit.mk0 A.det hA_det_ne_zero
  have hBA1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA_det_isUnit

  have hBA : A.transpose * (A⁻¹).transpose = 1 := by
    have h : A.transpose * (A⁻¹).transpose = (A⁻¹ * A).transpose := by
      rw [←Matrix.transpose_mul] <;> rfl
    rw [h, hBA1] <;> simp
  let c : Fin n → ℂ := (A⁻¹).transpose.mulVec w
  let h : TestFunction := ∑ i : Fin n, c i • f i
  use h
  intro j
  have h_melin : melinTransform h (s j) = ∑ i : Fin n, c i * melinTransform (f i) (s j) :=
    melinTransform_finset_sum (Finset.univ : Finset (Fin n)) f c (s j)
  rw [h_melin]
  have h3 : ∑ i : Fin n, c i * melinTransform (f i) (s j) = ∑ i : Fin n, c i * A i j := by
    apply Finset.sum_congr rfl
    intro i _
    simpa [A] using rfl
  rw [h3]
  have h4 : ∑ i : Fin n, c i * A i j = (A.transpose.mulVec c) j := by
    have h5 : ∑ i : Fin n, c i * A i j = ∑ i : Fin n, A i j * c i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h5]
    rfl
  rw [h4]
  have h6 : A.transpose.mulVec c = w := by
    have h7 : A.transpose.mulVec c = (A.transpose * (A⁻¹).transpose).mulVec w := by
      rw [Matrix.mulVec_mulVec] <;> rfl
    rw [h7, hBA] <;> simp
  rw [h6]

end RHSpectralDuality
end OrderPreservingBijection
