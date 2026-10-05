import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma small_finite : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1}
  have h_up_fin : S_up.Finite := finite_of_encard_le (hC1 1 (by norm_num))
  let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im ≤ 0}
  have h_low_fin : S_low.Finite := by
    have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
      ext s
      simp only [S_up, S_low, Set.mem_image]
      constructor
      · intro h
        refine ⟨star s, ?_, by simp⟩
        have h_zeta : _root_.riemannZeta (star s) = 0 := by rw [riemannZeta_conj, h.1]; simp
        have h_im1 : 0 ≤ (star s).im := by simp [Complex.ext_iff] at h ⊢ <;> linarith
        have h_im2 : (star s).im ≤ 1 := by simp [Complex.ext_iff] at h ⊢ <;> linarith
        exact ⟨h_zeta, h.2.1, h.2.2.1, h_im1, h_im2⟩
      · rintro ⟨t, ht, rfl⟩
        have h_zeta : _root_.riemannZeta (star t) = 0 := by rw [riemannZeta_conj, ht.1]; simp
        have h_im1 : -1 ≤ (star t).im := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
        have h_im2 : (star t).im ≤ 0 := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
        exact ⟨h_zeta, ht.2.1, ht.2.2.1, h_im1, h_im2⟩
    rw [h_conj_map]
    exact h_up_fin.image _
  have h_band : {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} ⊆ S_up ∪ S_low := by
    intro s hs
    have h2 : |s.im| < 1 := hs.2.2.2
    have h2' : -1 < s.im ∧ s.im < 1 := abs_lt.mp h2
    by_cases h3 : 0 ≤ s.im
    · left; exact ⟨hs.1, hs.2.1, hs.2.2.1, h3, by linarith⟩
    · right
      have h4 : s.im < 0 := by linarith
      have h5 : -1 ≤ s.im := by linarith
      have h6 : s.im ≤ 0 := by linarith
      have h_goal : _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im ≤ 0 :=
        ⟨hs.1, hs.2.1, hs.2.2.1, h5, h6⟩
      simpa [S_low] using h_goal
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
    intro n _ m _ h; exact nontrivialZeroEnum_injective h
  exact Set.Finite.of_finite_image h_img_fin h_inj

#check small_finite

end RHSpectralDuality
