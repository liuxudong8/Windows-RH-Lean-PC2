import OrderPreservingBijection.test_exists_n
import OrderPreservingBijection.test_interval_indicator

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助引理：区间 [a^i, a^{i+1}] 的 Mellin 变换。
    M[1_{[a^i, a^{i+1}]}](s) = (a^s)^i * (a^s - 1) / s -/
lemma mellin_interval_pow (a : ℝ) (ha : 1 < a) (i : ℕ) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator (a ^ i) (a ^ (i + 1))
      (by positivity) (by gcongr <;> linarith)) s =
    (Complex.exp (s * (Real.log a : ℂ))) ^ i * (Complex.exp (s * (Real.log a : ℂ)) - 1) / s := by
  set v : ℂ := Complex.exp (s * (Real.log a : ℂ)) with hv_def
  have h_pos1 : 0 < a ^ i := by positivity
  have h_pos2 : 0 < a ^ (i + 1) := by positivity
  have h_lt : a ^ i < a ^ (i + 1) := by
    have h1 : 1 < a := ha
    have h2 : a ^ i < a ^ (i + 1) := by
      have h3 : a ^ (i + 1) = a ^ i * a := by
        simp [pow_succ] <;> ring
      rw [h3]
      have h4 : 0 < a ^ i := by positivity
      nlinarith
    exact h2
  rw [intervalIndicator_mellinTransform (a ^ i) (a ^ (i + 1)) h_pos1 h_lt s hs]
  have h_log1 : Real.log (a ^ (i + 1)) = ((i + 1 : ℕ) : ℝ) * Real.log a := Real.log_pow a (i + 1)
  have h_log2 : Real.log (a ^ i) = (i : ℝ) * Real.log a := Real.log_pow a i
  rw [h_log1, h_log2]
  have h_eq1 : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) := by
    have h5 : s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ) = ((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ)) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h5]
    rw [Complex.exp_nat_mul (s * (Real.log a : ℂ)) (i + 1)]
    <;> rfl
  have h_eq2 : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ i := by
    have h5 : s * ((i : ℝ) * Real.log a : ℂ) = (i : ℂ) * (s * (Real.log a : ℂ)) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h5]
    rw [Complex.exp_nat_mul (s * (Real.log a : ℂ)) i]
    <;> rfl
  rw [h_eq1, h_eq2]
  have h6 : v ^ (i + 1) - v ^ i = v ^ i * (v - 1) := by
    have h7 : v ^ (i + 1) = v ^ i * v := by
      simp [pow_succ] <;> ring
    rw [h7] <;> ring
  rw [h6] <;> ring

/-- n 点 Mellin 有限插值（定理，零 sorry）：
    对任意有限点集 s : Fin n → ℂ（两两不同且非零），任意赋值 w : Fin n → ℂ，
    存在 TestFunction h 使 M[h](s i) = w i。 -/
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
    intervalIndicator (a ^ (i : ℕ)) (a ^ ((i : ℕ) + 1)) (by positivity) (by gcongr <;> linarith)
  have h_matrix_eq : ∀ (i j : Fin n), melinTransform (f i) (s j) = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
    intro i j
    exact mellin_interval_pow a ha_gt_one (i : ℕ) (s j) (h_ne_zero j)
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => melinTransform (f i) (s j))
  let V : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j => (v j - 1) / (s j))
  have hA_eq_VD : A = V * D := by
    ext i j
    simp [A, V, D, Matrix.vandermonde, Matrix.mul_apply, h_matrix_eq, Finset.sum_ite_eq'] <;> ring
  have hV_det_ne_zero : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde v]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have h_j_gt_i : i < j := (Finset.mem_Ioi.mp hj)
    have h_ij : i ≠ j := by linarith
    have h_vj_ne_vi : v j ≠ v i := hv_distinct i j h_ij
    simpa [sub_ne_zero] using h_vj_ne_vi.symm
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
    exact Matrix.nonsing_inv_mul _ hA_det_ne_zero
  rcases hA_invertible with ⟨B, hBA⟩
  let c : Fin n → ℂ := fun i => ∑ k : Fin n, B i k * w k
  let h : TestFunction := ∑ i : Fin n, c i • f i
  use h
  intro j
  have h_melin : melinTransform h (s j) = ∑ i : Fin n, c i * melinTransform (f i) (s j) := by
    rw [melinTransform_finset_sum]
    <;> rfl
  rw [h_melin]
  have h_sum : ∑ i : Fin n, c i * melinTransform (f i) (s j) = w j := by
    have h9 : ∑ i : Fin n, c i * melinTransform (f i) (s j) = ∑ i : Fin n, (∑ k : Fin n, B i k * w k) * A i j := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [h9]
    have h10 : ∑ i : Fin n, (∑ k : Fin n, B i k * w k) * A i j = ∑ k : Fin n, w k * (∑ i : Fin n, B i k * A i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      <;> rfl
    rw [h10]
    have h11 : ∑ i : Fin n, B i k * A i j = (B * A) k j := by
      rfl
    have h12 : ∀ k : Fin n, ∑ i : Fin n, B i k * A i j = if k = j then (1 : ℂ) else 0 := by
      intro k
      rw [h11, hBA]
      simp [Matrix.one_apply]
      <;> aesop
    rw [Finset.sum_congr rfl (fun k _ => h12 k)]
    rw [Finset.sum_ite_eq'] <;> simp
  exact h_sum

end RHSpectralDuality
end OrderPreservingBijection
