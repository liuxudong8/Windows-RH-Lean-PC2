import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- Vandermonde 行列式非零当且仅当元素两两不同。 -/
lemma vandermonde_det_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv_distinct : ∀ i j, i ≠ j → v i ≠ v j) :
    (Matrix.vandermonde v).det ≠ 0 := by
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
  have h : v j - v i ≠ 0 := by exact?
  exact h

/-- 乘积非零。 -/
lemma product_det_ne_zero {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A * B).det ≠ 0 := by
  rw [Matrix.det_mul]
  intro h
  have h_mul : A.det = 0 ∨ B.det = 0 := mul_eq_zero.mp h
  cases h_mul with
  | inl hA' => exact hA hA'
  | inr hB' => exact hB hB'

/-- v j ≠ 1 → v j - 1 ≠ 0。 -/
lemma sub_one_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv_ne_one : ∀ j, v j ≠ 1) (j : Fin n) :
    v j - 1 ≠ 0 := by
  intro h
  have h3 : v j - 1 + (1 : ℂ) = v j := by exact?
  rw [h] at h3
  have h4 : (0 : ℂ) + (1 : ℂ) = v j := h3
  have h5 : (0 : ℂ) + (1 : ℂ) = (1 : ℂ) := by ring
  rw [h5] at h4
  have h2 : v j = 1 := Eq.symm h4
  exact hv_ne_one j h2

/-- Vandermonde 矩阵元素。 -/
lemma vandermonde_apply {n : ℕ} {v : Fin n → ℂ} (i j : Fin n) :
    (Matrix.vandermonde v) i j = (v i) ^ (j : ℕ) :=
  Matrix.vandermonde_apply v i j

/-- 乘积非零（ℂ）。 -/
lemma product_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro h
  have h' : a = 0 ∨ b = 0 := mul_eq_zero.mp h
  cases h' with
  | inl ha' => exact ha ha'
  | inr hb' => exact hb hb'

/-- 对角矩阵元素。 -/
lemma diagonal_apply {n : ℕ} {d : Fin n → ℂ} (j : Fin n) :
    (Matrix.diagonal d) j j = d j := by exact?

/-- det ≠ 0 → IsUnit det（在域 ℂ 中）。 -/
lemma det_ne_zero_implies_isUnit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.det ≠ 0) :
    IsUnit A.det := by
  apply isUnit_iff_exists_inv.mpr
  use (A.det)⁻¹
  field_simp [h]
  <;> ring

end RHSpectralDuality
end OrderPreservingBijection
