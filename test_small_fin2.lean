import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma small_finite : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1}
  have h_up_fin : S_up.Finite := finite_of_encard_le (hC1 1 (by norm_num))
  let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im < 0}
  have h_low_fin : S_low.Finite := by
    have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
      ext s
      simp only [S_up, S_low, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h
        refine ⟨star s, ?_, by simp⟩
        have h_zeta : _root_.riemannZeta (star s) = 0 := by
          rw [riemannZeta_conj, h.1]; simp
        exact ⟨h_zeta, h.2.1, h.2.2.1, by linarith [h.2.2.2], by linarith [h.2.2.2]⟩
      · rintro ⟨t, ht, rfl⟩
        have h_zeta : _root_.riemannZeta (star t) = 0 := by rw [riemannZeta_conj, ht.1]; simp
        exact ⟨h_zeta, ht.2.1, ht.2.2.1, by linarith [ht.2.2.2], by linarith [ht.2.2.2]⟩
    rw [h_conj_map]
    exact h_up_fin.image _
  have h_band : {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} ⊆ S_up ∪ S_low := by
    intro s hs
    have h2 : |s.im| < 1 := hs.2.2.2
    by_cases h3 : 0 ≤ s.im
    · left
      exact ⟨hs.1, hs.2.1, hs.2.2.1, h3, by
        have h4 : s.im ≤ 1 := by linarith [abs_lt.mp h2]
        exact h4⟩
    · right
      have h4 : s.im < 0 := by linarith
      exact ⟨hs.1, hs.2.1, hs.2.2.1, by linarith [abs_lt.mp h2], by linarith⟩
  have h_band_fin : ({s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1}).Finite :=
    (h_up_fin.union h_low_fin).subset h_band
  let img_set : Set ℂ := nontrivialZeroEnum '' ({n : ℕ | |(nontrivialZeroEnum n).im| < 1})
  have h_img_subset : img_set ⊆ {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} := by
    intro s hs
    rcases hs with ⟨n, hn, rfl⟩
    have h_z := nontrivialZeroEnum_are_zeros n
    exact ⟨h_z.1, h_z.2.1, h_z.2.2, hn⟩
  have h_img_fin : img_set.Finite := h_band_fin.subset h_img_subset
  have h_inj : Set.InjOn nontrivialZeroEnum ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}) := by
    intro n _ m _ h
    exact nontrivialZeroEnum_injective h
  exact Set.Finite.of_finite_image h_img_fin h_inj

#check small_finite

end RHSpectralDuality
