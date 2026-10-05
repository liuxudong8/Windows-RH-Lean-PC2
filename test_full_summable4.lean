import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

-- small 有限性
lemma small_finite : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := by
  let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1}
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  have h_up_fin : S_up.Finite := finite_of_encard_le (hC1 1 (by norm_num))
  let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im < 0}
  have h_low_fin : S_low.Finite := by
    have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
      ext s; simp [S_up, S_low, riemannZeta_conj] <;> constructor <;> intro h <;> simp [h] <;> tauto
    rw [h_conj_map]; exact h_up_fin.image _
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

-- 存在 k 使得 2^k ≤ t < 2^(k+1)
lemma exists_layer_index (t : ℝ) (ht : 1 ≤ t) : ∃ (k : ℕ), (2^k : ℝ) ≤ t ∧ t < (2^(k+1) : ℝ) := by
  have h_exists : ∃ k : ℕ, t < (2^(k+1) : ℝ) := by
    refine ⟨Nat.ceil (Real.logb 2 (t + 1)) + 1, ?_⟩
    have h1 : t + 1 ≤ (2 ^ (Nat.ceil (Real.logb 2 (t + 1))) : ℝ) := by
      have h4 : t + 1 = 2 ^ (Real.logb 2 (t + 1)) := by rw [Real.rpow_logb (by linarith) (by norm_num)]
      rw [h4]
      have h5 : Real.logb 2 (t + 1) ≤ (Nat.ceil (Real.logb 2 (t + 1)) : ℝ) := Nat.le_ceil _
      gcongr
    have h6 : (2 ^ (Nat.ceil (Real.logb 2 (t + 1))) : ℝ) < (2 ^ (Nat.ceil (Real.logb 2 (t + 1)) + 1) : ℝ) := by
      apply pow_lt_pow_right <;> norm_num
    linarith
  let k := Nat.find h_exists
  have h_k_prop : t < (2^(k+1) : ℝ) := Nat.find_spec h_exists
  have h_k_min : ∀ m < k, ¬(t < (2^(m+1) : ℝ)) := fun m hm => Nat.find_min h_exists hm
  have h_k_ge : (2^k : ℝ) ≤ t := by
    by_cases h_k0 : k = 0
    · rw [h_k0]; norm_num; linarith
    · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k0
      have h_pred : k - 1 < k := by omega
      have h_not : ¬(t < (2^((k-1)+1) : ℝ)) := h_k_min (k-1) h_pred
      have h_eq : (k - 1) + 1 = k := by omega
      rw [h_eq] at h_not; linarith
  exact ⟨k, h_k_ge, h_k_prop⟩

-- 完整定理
theorem zero_weighted_series_summable_test :
    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2) := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  rcases zero_multiplicity_log_growth with ⟨C2, hC2_pos, hC2⟩
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2
  let small : Set ℕ := {n | |(nontrivialZeroEnum n).im| < 1}
  let layer (k : ℕ) : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_small_fin : small.Finite := small_finite
  have h_layer_fin : ∀ k, (layer k).Finite := by
    intro k
    have h_encard := hC1 (2^(k+1)) (by positivity)
    exact finite_of_encard_le h_encard |>.subset (by
      intro n hn; simp [layer] at hn ⊢ <;> tauto)
  let C : ℝ := (16 * C1 + 2) * (C2 * 4 + 1)
  have h_layer_sum : ∀ k, ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
    intro k; exact layer_sum_bound C1 C2 hC1_pos hC2_pos hC1 hC2 k (h_layer_fin k)
  have h_summable_geom : Summable (fun k : ℕ => C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
    have h : Summable (fun k : ℕ => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := summable_quadratic_over_geometric
    simpa [mul_comm C] using Summable.mul_left C h
  let small_sum : ℝ := ∑ n ∈ h_small_fin.toFinset, w n
  let total_bound : ℝ := small_sum + ∑' k : ℕ, C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k
  have h_nonneg : ∀ n, 0 ≤ w n := by intro n; positivity
  have h_finite_bound : ∀ (s : Finset ℕ), ∑ n ∈ s, w n ≤ total_bound := by
    intro s
    by_cases hs : s.Nonempty
    · let M : ℝ := s.sup' hs (fun n => |(nontrivialZeroEnum n).im|)
      have hM : ∀ n ∈ s, |(nontrivialZeroEnum n).im| ≤ M := by
        intro n hn; exact Finset.le_sup' (f := fun n => |(nontrivialZeroEnum n).im|) hn
      have hK : ∃ (K : ℕ), M < (2^(K+1) : ℝ) := by
        refine ⟨Nat.ceil (Real.logb 2 (M + 1)) + 1, ?_⟩
        have h1 : M + 1 ≤ (2 ^ (Nat.ceil (Real.logb 2 (M + 1))) : ℝ) := by
          have h4 : M + 1 = 2 ^ (Real.logb 2 (M + 1)) := by rw [Real.rpow_logb (by linarith) (by norm_num)]
          rw [h4]
          have h5 : Real.logb 2 (M + 1) ≤ (Nat.ceil (Real.logb 2 (M + 1)) : ℝ) := Nat.le_ceil _
          gcongr
        have h6 : (2 ^ (Nat.ceil (Real.logb 2 (M + 1))) : ℝ) < (2 ^ (Nat.ceil (Real.logb 2 (M + 1)) + 1) : ℝ) := by
          apply pow_lt_pow_right <;> norm_num
        linarith
      rcases hK with ⟨K, hK⟩
      let t : Finset ℕ := h_small_fin.toFinset ∪ Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset)
      have h_subset : s ⊆ t := by
        intro n hn
        have h_im : |(nontrivialZeroEnum n).im| ≤ M := hM n hn
        by_cases h_small : n ∈ small
        · simp [t, h_small]; tauto
        · have h_im1 : (1 : ℝ) ≤ |(nontrivialZeroEnum n).im| := by
            have h' : ¬(|(nontrivialZeroEnum n).im| < 1) := by simpa [small] using h_small
            linarith
          rcases exists_layer_index |(nontrivialZeroEnum n).im| h_im1 with ⟨k, hk1, hk2⟩
          have h_k_le_K : k ≤ K := by
            by_contra h_gt
            have h_gt' : K < k := by omega
            have h_im_ge : (2^(K+1) : ℝ) ≤ |(nontrivialZeroEnum n).im| := by
              have h : (2^(K+1) : ℝ) ≤ (2^k : ℝ) := by apply pow_le_pow_right <;> norm_num <;> omega
              linarith
            linarith
          have h_k_in : k ∈ Finset.range (K + 1) := by simp [Finset.mem_range]; omega
          simp [t, h_k_in, hk1, hk2, Set.Finite.mem_toFinset] <;> tauto
      have h_sum_le : ∑ n ∈ s, w n ≤ ∑ n ∈ t, w n := Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun i _ _ => h_nonneg i)
      have h_disj : ∀ k ∈ Finset.range (K + 1), Disjoint h_small_fin.toFinset ((h_layer_fin k).toFinset) := by
        intro k _
        simp [Finset.disjoint_left, small, layer, Set.Finite.mem_toFinset] <;> intro n hn1 hn2 <;> linarith
      have h_disj2 : ∀ k1 k2, k1 ≠ k2 → Disjoint ((h_layer_fin k1).toFinset) ((h_layer_fin k2).toFinset) := by
        intro k1 k2 hne
        simp [Finset.disjoint_left, layer, Set.Finite.mem_toFinset] <;> intro n hn1 hn2
        have h1 : (2^k1 : ℝ) ≤ |(nontrivialZeroEnum n).im| := hn1.1
        have h2 : |(nontrivialZeroEnum n).im| < (2^(k1+1) : ℝ) := hn1.2
        have h3 : (2^k2 : ℝ) ≤ |(nontrivialZeroEnum n).im| := hn2.1
        wlog hkm : k1 < k2 generalizing k1 k2
        · exact (this k2 k1 (Ne.symm hne) (by omega)).symm
        · have h4 : (2^(k1+1) : ℝ) ≤ (2^k2 : ℝ) := by apply pow_le_pow_right <;> norm_num <;> omega
          linarith
      have h_sum_t : ∑ n ∈ t, w n = small_sum + ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n := by
        simp [t, Finset.sum_union, h_disj, Finset.sum_biUnion, h_disj2] <;> ring
      rw [h_sum_t] at h_sum_le
      have h_geom_le : ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ ∑ k ∈ Finset.range (K + 1), C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
        apply Finset.sum_le_sum; intro k _; exact h_layer_sum k
      have h_tsum_le : ∑ k ∈ Finset.range (K + 1), C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k ≤ ∑' k : ℕ, C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
        exact Finset.sum_le_tsum (Finset.range (K + 1)) (fun k _ => by positivity) h_summable_geom
      linarith
    · have h_empty : s = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hs
      rw [h_empty]; simp [total_bound, small_sum]; positivity
  have h_range_bound : ∀ (N : ℕ), ∑ n ∈ Finset.range N, w n ≤ total_bound := by
    intro N; exact h_finite_bound (Finset.range N)
  exact summable_of_sum_range_le h_nonneg h_range_bound

#check zero_weighted_series_summable_test

end RHSpectralDuality
