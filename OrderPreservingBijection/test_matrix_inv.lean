import OrderPreservingBijection.test_exists_n
import OrderPreservingBijection.test_mellin_pow4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- n 点插值矩阵可逆。 -/
lemma n_point_matrix_invertible (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0)
    (a : ℝ) (ha_gt_one : 1 < a)
    (h_a_ne_one : ∀ i, Complex.exp (s i * (Real.log a : ℂ)) ≠ 1)
    (h_a_distinct : ∀ i j, i ≠ j → Complex.exp (s i * (Real.log a : ℂ)) ≠ Complex.exp (s j * (Real.log a : ℂ))) :
    let v : Fin n → ℂ := fun j => Complex.exp (s j * (Real.log a : ℂ))
    let f : Fin n → TestFunction := fun i =>
      intervalIndicator (a ^ (i : ℕ)) (a ^ ((i : ℕ) + 1)) (by positivity) (pow_lt_pow_succ a ha_gt_one (i : ℕ))
    let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => melinTransform (f i) (s j))
    A.det ≠ 0 := by
  let v : Fin n → ℂ := fun j => Complex.exp (s j * (Real.log a : ℂ))
  let f : Fin n → TestFunction := fun i =>
    intervalIndicator (a ^ (i : ℕ)) (a ^ ((i : ℕ) + 1)) (by positivity) (pow_lt_pow_succ a ha_gt_one (i : ℕ))
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => melinTransform (f i) (s j))
  let V : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j => (v j - 1) / (s j))
  have hv_ne_one : ∀ j, v j ≠ 1 := by
    intro j
    simpa [v] using h_a_ne_one j
  have hv_distinct : ∀ i j, i ≠ j → v i ≠ v j := by
    intro i j hne
    simpa [v] using h_a_distinct i j hne
  have h_matrix_eq : ∀ (i j : Fin n), melinTransform (f i) (s j) = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
    intro i j
    exact mellin_interval_pow a ha_gt_one (i : ℕ) (s j) (h_ne_zero j)
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
      have hVij : V i j = (v j) ^ (i : ℕ) := by
        simp [V, Matrix.vandermonde]
      have hDjj : D j j = (v j - 1) / (s j) := by
        simp [D, Matrix.diagonal]
      rw [hVij, hDjj] <;> ring
    have h2 : A i j = melinTransform (f i) (s j) := by simp [A]
    rw [h2, h_matrix_eq, h1]
  have hV_det_ne_zero : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde v]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have h_j_gt_i : i < j := Finset.mem_Ioi.mp hj
    have h_ij : i ≠ j := by
      intro h_eq
      have h_cont : j < j := by
        rw [h_eq] at h_j_gt_i
        exact h_j_gt_i
      exact lt_irrefl j h_cont
    have h_vj_ne_vi : v j ≠ v i := hv_distinct i j h_ij
    have h : v j - v i ≠ 0 := by
      intro h4
      exact h_vj_ne_vi (by simpa using h4)
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
    have h_mul : V.det * D.det ≠ 0 := by exact?
    exact h_mul
  exact hA_det_ne_zero

end RHSpectralDuality
end OrderPreservingBijection
