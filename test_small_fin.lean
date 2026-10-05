import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 先验证 small 有限
lemma small_finite : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := by
  have h1 : Set.Finite {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} := by
    have h_upper := zero_counting_estimate 1 (by norm_num)
    have h_upper_fin : Set.Finite {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1} :=
      finite_of_encard_le h_upper
    have h_lower_fin : Set.Finite {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im < 0} := by
      have h_conj : Set.Finite {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1} := h_upper_fin
      exact h_conj.image (fun s => star s) |>.subset (by intro s hs; simp at hs ⊢ <;> tauto)
    sorry
  sorry

#check small_finite

end RHSpectralDuality
