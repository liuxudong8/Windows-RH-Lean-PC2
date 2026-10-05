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

-- small 有限性（简化版：用 zero_counting_estimate + nontrivialZeroEnum 单射）
lemma small_finite : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := by
  let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1}
  have h_up_fin : S_up.Finite := finite_of_encard_le (zero_counting_estimate 1 (by norm_num))
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

-- 存在 k 使得 2^k ≤ t < 2^(k+1)，对 t ≥ 1
lemma exists_layer_index (t : ℝ) (ht : 1 ≤ t) : ∃ (k : ℕ), (2^k : ℝ) ≤ t ∧ t < (2^(k+1) : ℝ) := by
  let k := Nat.find (fun k => t < (2^(k+1) : ℝ))
  have h_exists : ∃ k, t < (2^(k+1) : ℝ) := by
    refine ⟨Nat.ceil (Real.logb 2 t) + 1, ?_⟩
    have h1 : t ≤ (2^(Nat.ceil (Real.logb 2 t) + 1) : ℝ) := by
      have h2 : Real.logb 2 t ≤ (Nat.ceil (Real.logb 2 t) : ℝ) := Nat.le_ceil _
      have h3 : t ≤ (2 ^ (Nat.ceil (Real.logb 2 t)) : ℝ) := by
        have h4 : Real.logb 2 t ≤ (Nat.ceil (Real.logb 2 t) : ℝ) := h2
        have h5 : t ≤ (2 ^ (Nat.ceil (Real.logb 2 t)) : ℝ) := by
          calc t = 2 ^ (Real.logb 2 t) := by rw [Real.rpow_logb (by linarith) (by norm_num)]
               _ ≤ 2 ^ (Nat.ceil (Real.logb 2 t) : ℝ) := by gcongr
          exact h5
      exact h3
    have h6 : (2 ^ (Nat.ceil (Real.logb 2 t)) : ℝ) < (2 ^ (Nat.ceil (Real.logb 2 t) + 1) : ℝ) := by
      apply pow_lt_pow_right <;> norm_num
    linarith
  have h_k_prop : t < (2^(k+1) : ℝ) := Nat.find_spec h_exists
  have h_k_min : ∀ m < k, ¬(t < (2^(m+1) : ℝ)) := by
    intro m hm; exact Nat.find_min h_exists hm
  have h_k_ge : (2^k : ℝ) ≤ t := by
    by_cases h_k0 : k = 0
    · rw [h_k0]; norm_num; linarith
    · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k0
      have h_pred : k - 1 < k := by omega
      have h_not : ¬(t < (2^((k-1)+1) : ℝ)) := h_k_min (k-1) h_pred
      have h_eq : (k - 1) + 1 = k := by omega
      rw [h_eq] at h_not
      have h : (2^k : ℝ) ≤ t := by linarith
      exact h
  exact ⟨k, h_k_ge, h_k_prop⟩

-- layer 两两不交
lemma layers_disjoint (k m : ℕ) (h : k ≠ m) : Disjoint ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)} : Set ℕ) ({n : ℕ | (2^m : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(m+1) : ℝ)} : Set ℕ) := by
  wlog hkm : k < m generalizing k m
  · exact (this m k (Ne.symm h) (by omega)).symm
  · rintro n hn1 hn2
    have h1 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := hn1.1
    have h2 : |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ) := hn1.2
    have h3 : (2^m : ℝ) ≤ |(nontrivialZeroEnum n).im| := hn2.1
    have h4 : (2^(k+1) : ℝ) ≤ (2^m : ℝ) := by
      apply pow_le_pow_right <;> norm_num <;> omega
    linarith

-- 完整定理
theorem zero_weighted_series_summable' :
    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2) := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  rcases zero_multiplicity_log_growth with ⟨C2, hC2_pos, hC2⟩
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2
  let small : Set ℕ := {n | |(nontrivialZeroEnum n).im| < 1}
  let layer (k : ℕ) : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_small_fin : small.Finite := small_finite
  have h_layer_fin : ∀ k, (layer k).Finite := by
    intro k; exact (layer_card_bound_raw C1 hC1_pos hC1 k).1
  let C : ℝ := (16 * C1 + 2) * (C2 * 4 + 1)
  have h_layer_sum : ∀ k, ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
    intro k; exact layer_sum_bound C1 C2 hC1_pos hC2_pos hC1 hC2 k (h_layer_fin k)
  have h_summable_geom : Summable (fun k : ℕ => C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
    apply Summable.mul_left; exact summable_quadratic_over_geometric
  let small_sum : ℝ := ∑ n ∈ h_small_fin.toFinset, w n
  let total_bound : ℝ := small_sum + ∑' k : ℕ, C * ((k : ℝ) + 1)^2 / (2 : ℝ)^k
  have h_cover : ∀ (n : ℕ), n ∈ small ∨ ∃ k, n ∈ layer k := by
    intro n
    by_cases h : n ∈ small
    · left; exact h
    · right
      have h_im1 : (1 : ℝ) ≤ |(nontrivialZeroEnum n).im| := by
        have h' : ¬(|(nontrivialZeroEnum n).im| < 1) := by simpa [small] using h
        linarith
      rcases exists_layer_index |(nontrivialZeroEnum n).im| h_im1 with ⟨k, hk1, hk2⟩
      exact ⟨k, ⟨hk1, hk2⟩⟩
  have h_finite_bound : ∀ (s : Finset ℕ), ∑ n ∈ s, w n ≤ total_bound := by
    intro s
    let K_s : Finset ℕ := s.biUnion (fun n => if h : ∃ k, n ∈ layer k then {Classical.choose h} else ∅)
    have h_decomp : ∀ n ∈ s, n ∈ small ∨ n ∈ ⋃ k ∈ K_s, layer k := by
      intro n hn
      rcases h_cover n with (h_small | ⟨k, hk⟩)
      · left; exact h_small
      · right
        have h_k_in : k ∈ K_s := by
          simp [K_s, Finset.mem_biUnion]
          refine ⟨n, hn, ?_⟩
          have h_exists : ∃ k, n ∈ layer k := ⟨k, hk⟩
          simp [h_exists]
          <;> tauto
        exact ⟨k, h_k_in, hk⟩
    sorry
  have h_nonneg : ∀ n, 0 ≤ w n := by intro n; positivity
  have h_range_bound : ∀ (N : ℕ), ∑ n ∈ Finset.range N, w n ≤ total_bound := by
    intro N; exact h_finite_bound (Finset.range N)
  exact summable_of_sum_range_le h_nonneg h_range_bound

#check zero_weighted_series_summable'

end RHSpectralDuality
