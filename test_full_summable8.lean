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
    rw [h_conj_map]; exact h_up_fin.image _
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

lemma exists_layer_index (t : ℝ) (ht : 1 ≤ t) : ∃ (k : ℕ), (2^k : ℝ) ≤ t ∧ t < (2^(k+1) : ℝ) := by
  have h_pos : 0 < t + 1 := by linarith
  let N := Nat.ceil (Real.logb 2 (t + 1))
  have h1 : (2 : ℝ) ^ (Real.logb 2 (t + 1)) = t + 1 :=
    Real.rpow_logb (b := (2 : ℝ)) (x := t + 1) (by norm_num) (by norm_num) h_pos
  have h2 : Real.logb 2 (t + 1) ≤ (N : ℝ) := Nat.le_ceil _
  have h3 : (2 : ℝ) ^ (Real.logb 2 (t + 1)) ≤ (2 : ℝ) ^ (N : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le <;> norm_num <;> exact h2
  have h4 : t + 1 ≤ (2 : ℝ) ^ (N : ℝ) := by
    calc t + 1 = (2 : ℝ) ^ (Real.logb 2 (t + 1)) := h1.symm
         _ ≤ (2 : ℝ) ^ (N : ℝ) := h3
  have h5 : (2 : ℝ) ^ (N : ℝ) = (2^N : ℝ) := by norm_cast
  have h6 : t + 1 ≤ (2^N : ℝ) := by rw [← h5]; exact h4
  have h7 : t < (2^N : ℝ) := by linarith
  have h8 : (2^N : ℝ) ≤ (2^(N+1) : ℝ) := by
    have h9 : (2^N : ℝ) * 2 = (2^(N+1) : ℝ) := by simp [pow_succ]
    have h10 : (2^N : ℝ) ≤ (2^N : ℝ) * 2 := by
      have h11 : (0 : ℝ) ≤ (2^N : ℝ) := by positivity
      nlinarith
    rw [h9] at h10; exact h10
  have h_exists : ∃ k : ℕ, t < (2^(k+1) : ℝ) := ⟨N, by linarith⟩
  let k := Nat.find h_exists
  have h_k_prop : t < (2^(k+1) : ℝ) := Nat.find_spec h_exists
  have h_k_min : ∀ m < k, ¬(t < (2^(m+1) : ℝ)) := fun m hm => Nat.find_min h_exists hm
  have h_k_ge : (2^k : ℝ) ≤ t := by
    by_cases h_k0 : k = 0
    · rw [h_k0]; norm_num; linarith
    · have h_pred : k - 1 < k := by omega
      have h_not : ¬(t < (2^((k-1)+1) : ℝ)) := h_k_min (k-1) h_pred
      have h_eq : (k - 1) + 1 = k := by omega
      rw [h_eq] at h_not
      have h' : (2^k : ℝ) ≤ t := by linarith
      exact h'
  exact ⟨k, h_k_ge, h_k_prop⟩

theorem zero_weighted_series_summable' :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  rcases zero_multiplicity_log_growth with ⟨C2, hC2_pos, hC2⟩
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2
  let small : Set ℕ := {n | |(nontrivialZeroEnum n).im| < 1}
  let layer : ℕ → Set ℕ := fun k => {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_small_fin : small.Finite := small_finite
  have h_layer_fin : ∀ k, (layer k).Finite := by
    intro k
    have h1 : (layer k) ⊆ {n : ℕ | |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)} := by
      intro n hn; exact hn.2
    have h2 : ({n : ℕ | |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite := by
      let T := (2^(k+1) : ℝ)
      have hT_pos : 0 < (2^(k+1) : ℝ) := by positivity
      let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
      have h_up_fin : S_up.Finite := finite_of_encard_le (hC1 T hT_pos)
      let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0}
      have h_low_fin : S_low.Finite := by
        have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
          ext s
          simp only [S_up, S_low, Set.mem_image]
          constructor
          · intro h
            refine ⟨star s, ?_, by simp⟩
            have h_zeta : _root_.riemannZeta (star s) = 0 := by rw [riemannZeta_conj, h.1]; simp
            have h_im1 : 0 ≤ (star s).im := by simp [Complex.ext_iff] at h ⊢ <;> linarith
            have h_im2 : (star s).im ≤ T := by simp [Complex.ext_iff] at h ⊢ <;> linarith
            exact ⟨h_zeta, h.2.1, h.2.2.1, h_im1, h_im2⟩
          · rintro ⟨t, ht, rfl⟩
            have h_zeta : _root_.riemannZeta (star t) = 0 := by rw [riemannZeta_conj, ht.1]; simp
            have h_im1 : -T ≤ (star t).im := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
            have h_im2 : (star t).im ≤ 0 := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
            exact ⟨h_zeta, ht.2.1, ht.2.2.1, h_im1, h_im2⟩
        rw [h_conj_map]; exact h_up_fin.image _
      have h_band : {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T} ⊆ S_up ∪ S_low := by
        intro s hs
        have h2 : |s.im| < T := hs.2.2.2
        have h2' : -T < s.im ∧ s.im < T := abs_lt.mp h2
        by_cases h3 : 0 ≤ s.im
        · left; exact ⟨hs.1, hs.2.1, hs.2.2.1, h3, by linarith⟩
        · right
          have h4 : s.im < 0 := by linarith
          have h5 : -T ≤ s.im := by linarith
          have h6 : s.im ≤ 0 := by linarith
          have h_goal : _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0 :=
            ⟨hs.1, hs.2.1, hs.2.2.1, h5, h6⟩
          simpa [S_low] using h_goal
      have h_band_fin : ({s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T}).Finite :=
        (h_up_fin.union h_low_fin).subset h_band
      let img_set : Set ℂ := nontrivialZeroEnum '' ({n : ℕ | |(nontrivialZeroEnum n).im| < T})
      have h_img_subset : img_set ⊆ {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T} := by
        intro s hs
        rcases hs with ⟨n, hn, rfl⟩
        have h_z := nontrivialZeroEnum_are_zeros n
        exact ⟨h_z.1, h_z.2.1, h_z.2.2, hn⟩
      have h_img_fin : img_set.Finite := h_band_fin.subset h_img_subset
      have h_inj : Set.InjOn nontrivialZeroEnum ({n : ℕ | |(nontrivialZeroEnum n).im| < T}) := by
        intro n _ m _ h; exact nontrivialZeroEnum_injective h
      exact Set.Finite.of_finite_image h_img_fin h_inj
    exact h2.subset h1
  let C := (16 * C1 + 2) * (C2 * 4 + 1)
  have h_layer_sum : ∀ k, ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ C * (k + 1)^2 / 2^k := by
    intro k
    exact layer_sum_bound C1 C2 hC1_pos hC2_pos hC1 hC2 k (h_layer_fin k)
  let g : ℕ → ℝ := fun (k : ℕ) => C * ((k : ℝ) + 1)^2 / 2^k
  have h_nonneg_g : ∀ k, 0 ≤ g k := by intro k; positivity
  have h_summable_geom : Summable g := by
    have h : Summable (fun k : ℕ => ((k : ℝ) + 1)^2 / (2^k : ℝ)) := summable_quadratic_over_geometric
    have h' : g = fun k => C * (((k : ℝ) + 1)^2 / (2^k : ℝ)) := by
      funext k; field_simp [g]; ring
    rw [h']
    exact Summable.mul_left C h
  have h_nonneg_w : ∀ n, 0 ≤ w n := by intro n; positivity
  let B := (∑ n ∈ h_small_fin.toFinset, w n) + ∑' k : ℕ, g k
  have h_range_bound : ∀ N : ℕ, ∑ i ∈ Finset.range N, w i ≤ B := by
    intro N
    let s := Finset.range N
    let M := s.fold max 0 (fun n => |(nontrivialZeroEnum n).im|)
    have hM_in : ∀ n ∈ s, |(nontrivialZeroEnum n).im| ≤ M := by
      intro n hn
      rw [Finset.le_fold_max]
      right
      exact ⟨n, hn, by linarith⟩
    by_cases hM_lt1 : M < 1
    · have h_sub : s ⊆ h_small_fin.toFinset := by
        intro n hn
        have h2 : |(nontrivialZeroEnum n).im| ≤ M := hM_in n hn
        have h3 : |(nontrivialZeroEnum n).im| < 1 := by linarith
        simpa [small, Set.Finite.mem_toFinset] using h3
      have h4 : ∑ n ∈ s, w n ≤ ∑ n ∈ h_small_fin.toFinset, w n :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
      have h5 : 0 ≤ ∑' k : ℕ, g k := by positivity
      have h6 : ∑ n ∈ h_small_fin.toFinset, w n ≤ B := by
        dsimp only [B]; linarith
      linarith
    · have hM_ge1 : 1 ≤ M := by linarith
      rcases exists_layer_index M hM_ge1 with ⟨K, hK1, hK2⟩
      let U := h_small_fin.toFinset ∪ (Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset))
      have h_cover : s ⊆ U := by
        intro n hn
        have h2 : |(nontrivialZeroEnum n).im| ≤ M := hM_in n hn
        by_cases h3 : |(nontrivialZeroEnum n).im| < 1
        · have h4 : n ∈ h_small_fin.toFinset := by
            simpa [small, Set.Finite.mem_toFinset] using h3
          exact Finset.mem_union_left _ h4
        · have h4 : 1 ≤ |(nontrivialZeroEnum n).im| := by linarith
          rcases exists_layer_index |(nontrivialZeroEnum n).im| h4 with ⟨k, hk1, hk2⟩
          have h5 : k ≤ K := by
            by_contra h6
            have h7 : K < k := by omega
            have h8 : (2^(K+1) : ℝ) ≤ (2^k : ℝ) := by
              apply pow_le_pow_right₀ <;> norm_num <;> omega
            have h9 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := hk1
            have h10 : (2^(K+1) : ℝ) ≤ |(nontrivialZeroEnum n).im| := by linarith
            have h11 : |(nontrivialZeroEnum n).im| < (2^(K+1) : ℝ) := by linarith [hK2, h2]
            linarith
          have h6 : k ∈ Finset.range (K + 1) := by simp [Finset.mem_range]; omega
          have h7 : n ∈ (h_layer_fin k).toFinset := by
            simpa [layer, Set.Finite.mem_toFinset] using ⟨hk1, hk2⟩
          have h8 : n ∈ Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset) :=
            Finset.mem_biUnion.mpr ⟨k, h6, h7⟩
          exact Finset.mem_union_right _ h8
      have h_disj_layers : ∀ k1 k2, k1 ≠ k2 → Disjoint ((h_layer_fin k1).toFinset) ((h_layer_fin k2).toFinset) := by
        intro k1 k2 hne
        rw [Finset.disjoint_left]
        intro n hn1 hn2
        have h1 : (2^k1 : ℝ) ≤ |(nontrivialZeroEnum n).im| := (by simpa [layer, Set.Finite.mem_toFinset] using hn1).1
        have h2 : |(nontrivialZeroEnum n).im| < (2^(k1+1) : ℝ) := (by simpa [layer, Set.Finite.mem_toFinset] using hn1).2
        have h3 : (2^k2 : ℝ) ≤ |(nontrivialZeroEnum n).im| := (by simpa [layer, Set.Finite.mem_toFinset] using hn2).1
        have h4 : |(nontrivialZeroEnum n).im| < (2^(k2+1) : ℝ) := (by simpa [layer, Set.Finite.mem_toFinset] using hn2).2
        by_cases h_lt : k1 < k2
        · have h5 : k1 + 1 ≤ k2 := by omega
          have h6 : (2^(k1+1) : ℝ) ≤ (2^k2 : ℝ) := by
            apply pow_le_pow_right₀ <;> norm_num <;> omega
          linarith
        · have h_ge : k2 ≤ k1 := by omega
          have h_eq : k2 < k1 := by omega
          have h5 : k2 + 1 ≤ k1 := by omega
          have h6 : (2^(k2+1) : ℝ) ≤ (2^k1 : ℝ) := by
            apply pow_le_pow_right₀ <;> norm_num <;> omega
          linarith
      have h_disj_small : Disjoint h_small_fin.toFinset (Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset)) := by
        rw [Finset.disjoint_left]
        intro n hn1 hn2
        have h9 : |(nontrivialZeroEnum n).im| < 1 := by simpa [small, Set.Finite.mem_toFinset] using hn1
        rcases Finset.mem_biUnion.mp hn2 with ⟨k, _, hnk⟩
        have h10 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := (by simpa [layer, Set.Finite.mem_toFinset] using hnk).1
        have h11 : (1 : ℝ) ≤ (2^k : ℝ) := by
          have h12 : ∀ k : ℕ, (1 : ℝ) ≤ (2^k : ℝ) := by
            intro k; induction k <;> simp [*, pow_succ] <;> norm_num <;> linarith
          exact h12 k
        linarith
      have h_sum_layers : ∑ n ∈ (Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset)), w n =
          ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n := by
        rw [Finset.sum_biUnion]
        intro k _ k2 _ hne
        exact h_disj_layers k k2 hne
      have h_sum_U : ∑ n ∈ U, w n = (∑ n ∈ h_small_fin.toFinset, w n) + ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n := by
        rw [Finset.sum_union h_disj_small, h_sum_layers]
      have h4 : ∑ n ∈ s, w n ≤ ∑ n ∈ U, w n :=
        Finset.sum_le_sum_of_subset_of_nonneg h_cover (fun _ _ _ => by positivity)
      rw [h_sum_U] at h4
      have h7 : ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ ∑ k ∈ Finset.range (K + 1), g k := by
        apply Finset.sum_le_sum
        intro k _
        exact h_layer_sum k
      have h8 : ∑ k ∈ Finset.range (K + 1), g k ≤ ∑' k : ℕ, g k :=
        Summable.sum_le_tsum (Finset.range (K + 1)) (fun i _ => h_nonneg_g i) h_summable_geom
      have h10 : 0 ≤ ∑' k : ℕ, g k := by positivity
      linarith
  exact summable_of_sum_range_le h_nonneg_w h_range_bound

#check zero_weighted_series_summable'

end RHSpectralDuality
