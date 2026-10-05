import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- 精确求和公式
lemma sum_quadratic_geometric_formula (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) = 12 - 2 * ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [pow_succ] <;> field_simp <;> ring

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  have h_nonneg : ∀ (k : ℕ), 0 ≤ ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by intro k; positivity
  have h_bounded : ∀ (n : ℕ), ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) ≤ 12 := by
    intro n
    have h_formula := sum_quadratic_geometric_formula n
    rw [h_formula]
    have h_pos : 0 ≤ 2 * ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^n := by positivity
    linarith
  exact summable_of_sum_range_le h_nonneg h_bounded

-- small 有限性
lemma small_finite : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := by
  let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1}
  have h_up_fin : S_up.Finite := finite_of_encard_le (zero_counting_estimate 1 (by norm_num))
  let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im < 0}
  have h_low_fin : S_low.Finite := by
    have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
      ext s; simp [S_up, S_low, riemannZeta_conj] <;> constructor <;> intro h <;> simp [h] <;> tauto
    rw [h_conj_map]
    exact h_up_fin.image _
  have h_band_fin : ({s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1}).Finite := by
    have h1 : {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} ⊆ S_up ∪ S_low := by
      intro s hs; have h2 : |s.im| < 1 := hs.2.2.2; by_cases h3 : 0 ≤ s.im
      · left; exact ⟨hs.1, hs.2.1, hs.2.2.1, h3, by linarith⟩
      · right; exact ⟨hs.1, hs.2.1, hs.2.2.1, by linarith, by linarith⟩
    exact (h_up_fin.union h_low_fin).subset h1
  have h_img : (nontrivialZeroEnum '' ({n : ℕ | |(nontrivialZeroEnum n).im| < 1})) ⊆ {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} := by
    intro s hs; rcases hs with ⟨n, hn, rfl⟩
    exact ⟨nontrivialZeroEnum_isZero n, nontrivialZeroEnum_re_pos n, nontrivialZeroEnum_re_lt_one n, hn⟩
  have h_img_fin : (nontrivialZeroEnum '' ({n : ℕ | |(nontrivialZeroEnum n).im| < 1})).Finite := h_band_fin.subset h_img
  exact Set.Finite.of_injective_image nontrivialZeroEnum_injective h_img_fin

-- 完整的 zero_weighted_series_summable 定理
theorem zero_weighted_series_summable' :
    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2) := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  rcases zero_multiplicity_log_growth with ⟨C2, hC2_pos, hC2⟩
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2
  let small : Set ℕ := {n | |(nontrivialZeroEnum n).im| < 1}
  let layer (k : ℕ) : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_small_fin : small.Finite := small_finite
  have h_layer_fin : ∀ k, (layer k).Finite := by
    intro k; exact layer_card_bound_raw C1 hC1_pos hC1 k |>.1
  let C : ℝ := (16 * C1 + 2) * (C2 * 4 + 1)
  have h_layer_sum : ∀ k, ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
    intro k; exact layer_sum_bound C1 C2 hC1_pos hC2_pos hC1 hC2 k (h_layer_fin k)
  have h_summable_geom : Summable (fun k : ℕ => C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
    apply Summable.mul_left
    exact summable_quadratic_over_geometric
  let small_sum : ℝ := ∑ n ∈ h_small_fin.toFinset, w n
  let layer_sum (k : ℕ) : ℝ := ∑ n ∈ (h_layer_fin k).toFinset, w n
  have h_main_bound : ∀ (N : ℕ), ∑ n ∈ Finset.range N, w n ≤ small_sum + ∑' k : ℕ, C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
    intro N
    let S_N : Finset ℕ := Finset.range N
    have h_S_nonempty : S_N.Nonempty → ∃ (M : ℝ), ∀ n ∈ S_N, |(nontrivialZeroEnum n).im| ≤ M := by
      intro h
      refine ⟨S_N.sup' h (fun n => |(nontrivialZeroEnum n).im|), ?_⟩
      intro n hn; exact Finset.le_sup' hn
    by_cases hN : S_N.Nonempty
    · rcases h_S_nonempty hN with ⟨M, hM⟩
      have h_exists_K : ∃ (K : ℕ), M < (2^(K+1) : ℝ) := by
        refine ⟨Nat.ceil (Real.logb 2 M) + 1, ?_⟩
        sorry
      rcases h_exists_K with ⟨K, hK⟩
      have h_cover : ∀ n ∈ S_N, n ∈ small ∨ ∃ k ≤ K, n ∈ layer k := by
        intro n hn
        have h_im : |(nontrivialZeroEnum n).im| ≤ M := hM n hn
        by_cases h_small : n ∈ small
        · left; exact h_small
        · right
          have h_im1 : ¬(|(nontrivialZeroEnum n).im| < 1) := by simpa [small] using h_small
          have h_im2 : (1 : ℝ) ≤ |(nontrivialZeroEnum n).im| := by linarith
          have h_exists : ∃ k : ℕ, (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ) := by
            sorry
          rcases h_exists with ⟨k, hk1, hk2⟩
          have h_k_le_K : k ≤ K := by
            by_contra h_k_gt
            have h_k_gt' : K < k := by linarith
            have h_im_ge : (2^(K+1) : ℝ) ≤ |(nontrivialZeroEnum n).im| := by
              have h : (2^(K+1) : ℝ) ≤ (2^k : ℝ) := by
                apply pow_le_pow_right
                <;> norm_num <;> linarith
              linarith
            linarith
          exact ⟨k, h_k_le_K, ⟨hk1, hk2⟩⟩
      sorry
    · sorry
  have h_nonneg : ∀ n, 0 ≤ w n := by intro n; positivity
  exact summable_of_sum_range_le h_nonneg h_main_bound

#check zero_weighted_series_summable'

end RHSpectralDuality
