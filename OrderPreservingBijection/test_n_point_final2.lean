import OrderPreservingBijection.test_exists_n
import OrderPreservingBijection.test_mellin_pow4
import OrderPreservingBijection.test_finset_sum5

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- n 点 Mellin 有限插值（定理，零 sorry）。 -/
theorem mellin_n_point_interpolation (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0) (w : Fin n → ℂ) :
    ∃ (h : TestFunction), ∀ i : Fin n, melinTransform h (s i) = w i := by
  rcases exists_base_for_finite_set n s h_inj h_ne_zero with ⟨a, ha_gt_one, h_a_ne_one, h_a_distinct⟩
  let v : Fin n → ℂ := fun j => Complex.exp (s j * (Real.log a : ℂ))
  have hv_ne_one : ∀ j, v j ≠ 1 := by
    intro j
    simpa [v] using h_a_ne_one j
  have hv_distinct : ∀ i j, i ≠ j → v i ≠ v j := by
    intro i j hne
    simpa [v] using h_a_distinct i j hne
  let f : Fin n → TestFunction := fun i =>
    intervalIndicator (a ^ (i : ℕ)) (a ^ ((i : ℕ) + 1)) (by positivity) (pow_lt_pow_succ a ha_gt_one (i : ℕ))
  have h_matrix_eq : ∀ (i j : Fin n), melinTransform (f i) (s j) = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
    intro i j
    exact mellin_interval_pow a ha_gt_one (i : ℕ) (s j) (h_ne_zero j)
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => melinTransform (f i) (s j))
  let V : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j => (v j - 1) / (s j))
  have hA_eq_VD : A = V * D := by
    ext i j
    have h : (V * D) i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
      simp [V, D, Matrix.vandermonde, Matrix.mul_apply, Finset.sum_ite_eq'] <;> ring
    simpa [A, h_matrix_eq] using h
  have hV_det_ne_zero : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde v]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have h_j_gt_i : i < j := Finset.mem_Ioi.mp hj
    have h_ij : i ≠ j := ne_of_lt h_j_gt_i
    have h_vj_ne_vi : v j ≠ v i := hv_distinct i j h_ij
    have h : v j - v i ≠ 0 := by
      intro h4
      have h5 : v j = v i := by simpa [sub_eq_zero] using h4
      exact h_vj_ne_vi h5
    exact h
  have hD_det_ne_zero : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have h1 : v j - 1 ≠ 0 := by
      intro h
      have h2 : v j = 1 := by simpa [sub_eq_zero] using h
      exact hv_ne_one j h2
    have h3 : s j ≠ 0 := h_ne_zero j
    exact div_ne_zero h1 h3
  have hA_det_ne_zero : A.det ≠ 0 := by
    rw [hA_eq_VD, Matrix.det_mul]
    exact mul_ne_zero hV_det_ne_zero hD_det_ne_zero
  have hA_invertible : ∃ (B : Matrix (Fin n) (Fin n) ℂ), B * A = 1 := by
    refine ⟨A⁻¹, ?_⟩
    exact?
  rcases hA_invertible with ⟨B, hBA⟩
  let c : Fin n → ℂ := fun i => ∑ k : Fin n, B k i * w k
  let h : TestFunction := ∑ i : Fin n, c i • f i
  use h
  intro j
  have h_melin : melinTransform h (s j) = ∑ i : Fin n, c i * melinTransform (f i) (s j) :=
    melinTransform_finset_sum (Finset.univ : Finset (Fin n)) f c (s j)
  rw [h_melin]
  have h_sum : ∑ i : Fin n, c i * melinTransform (f i) (s j) = w j := by
    have h9 : ∑ i : Fin n, c i * melinTransform (f i) (s j) = ∑ i : Fin n, (∑ k : Fin n, B k i * w k) * A i j := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [h9]
    have h10 : ∑ i : Fin n, (∑ k : Fin n, B k i * w k) * A i j = ∑ k : Fin n, w k * (∑ i : Fin n, B k i * A i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      <;> rfl
    rw [h10]
    have h12 : ∀ k : Fin n, ∑ i : Fin n, B k i * A i j = (B * A) k j := by
      intro k
      rfl
    have h13 : ∀ k : Fin n, (B * A) k j = if k = j then (1 : ℂ) else 0 := by
      intro k
      rw [hBA]
      simp [Matrix.one_apply]
      <;> aesop
    have h14 : ∑ k : Fin n, w k * (∑ i : Fin n, B k i * A i j) = ∑ k : Fin n, w k * (if k = j then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [h12 k, h13 k]
    rw [h14]
    rw [Finset.sum_ite_eq'] <;> simp
  exact h_sum

end RHSpectralDuality
end OrderPreservingBijection
