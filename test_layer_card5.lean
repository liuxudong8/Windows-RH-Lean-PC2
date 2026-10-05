import OrderPreservingBijection.stage_4

namespace RHSpectralDuality

open OrderPreservingBijection

lemma ceil_le_add_one (x : ℝ) (hx : 0 ≤ x) : (Nat.ceil x : ℝ) ≤ x + 1 := by
  have h1 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  linarith

lemma star_inj (x y : ℂ) : star x = star y → x = y := by
  intro h; have h2 : star (star x) = star (star y) := by rw [h]
  have h3 : star (star x) = x := by simp
  have h4 : star (star y) = y := by simp
  rw [h3, h4] at h2; exact h2

lemma layer_card_bound_raw (C1 : ℝ) (hC1_pos : 0 < C1)
    (hC1 : ∀ (T : ℝ), 0 < T → Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat))
    (k : ℕ) (h_layer_fin : ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite) :
    (h_layer_fin.toFinset.card : ℝ) ≤ 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) := by
  let T := (2^(k+1) : ℝ)
  have hT_pos : 0 < T := by positivity
  let Upper : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
  let Lower : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0}
  let S_ℂ : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T}
  let preimage : Set ℕ := {n | |(nontrivialZeroEnum n).im| ≤ T}
  let layer_k : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_upper_encard : Set.encard Upper ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat) := hC1 T hT_pos
  have h_upper_fin : Upper.Finite := finite_of_encard_le h_upper_encard
  have h_eq_lower_upper : star '' Lower = Upper := lower_conj_eq_upper T
  have h_star_img_fin : (star '' Lower).Finite := by rw [h_eq_lower_upper]; exact h_upper_fin
  have h_lower_fin : Lower.Finite := finite_preimage_of_injective star_inj h_star_img_fin
  have h_S_fin : S_ℂ.Finite := by
    have h_decomp : S_ℂ ⊆ Upper ∪ Lower := by
      intro s hs; have him : |s.im| ≤ T := hs.2.2.2
      by_cases h : 0 ≤ s.im
      · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1, h, by linarith [abs_le.mp him]⟩
      · exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1, by linarith [abs_le.mp him], by linarith⟩
    exact Set.Finite.subset (Set.Finite.union h_upper_fin h_lower_fin) h_decomp
  have h_img_sub : nontrivialZeroEnum '' preimage ⊆ S_ℂ := by
    intro s hs; rcases hs with ⟨n, hn, rfl⟩
    have hz : _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧ 0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 := nontrivialZeroEnum_are_zeros n
    exact ⟨hz.1, hz.2.1, hz.2.2, hn⟩
  have h_preimg_fin : preimage.Finite := by
    have h_img_fin : (nontrivialZeroEnum '' preimage).Finite := Set.Finite.subset h_S_fin h_img_sub
    exact finite_preimage_of_injective nontrivialZeroEnum_injective h_img_fin
  have h_sub_layer : layer_k ⊆ preimage := by intro n hn; exact le_of_lt hn.2
  have h1 : h_layer_fin.toFinset.card ≤ h_preimg_fin.toFinset.card := by
    have h11 : h_layer_fin.toFinset ⊆ h_preimg_fin.toFinset := by
      intro x hx
      have h23 : x ∈ ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}) :=
        (Set.Finite.mem_toFinset).mp hx
      have h24 : x ∈ layer_k := h23
      have h25 : x ∈ preimage := h_sub_layer h24
      exact (Set.Finite.mem_toFinset).mpr h25
    exact Finset.card_le_card h11
  have h_img_fin : (nontrivialZeroEnum '' preimage).Finite := Set.Finite.subset h_S_fin h_img_sub
  have h_eq_img : h_img_fin.toFinset = Finset.image nontrivialZeroEnum h_preimg_fin.toFinset :=
    Set.Finite.toFinset_image nontrivialZeroEnum h_preimg_fin h_img_fin
  have h2 : h_preimg_fin.toFinset.card = h_img_fin.toFinset.card := by
    rw [h_eq_img, Finset.card_image_of_injOn]
    <;> exact fun x _ y _ hxy => nontrivialZeroEnum_injective hxy
  have h3 : h_img_fin.toFinset ⊆ h_S_fin.toFinset := by
    intro z hz; have h4 : z ∈ nontrivialZeroEnum '' preimage := (Set.Finite.mem_toFinset).mp hz
    have h5 : z ∈ S_ℂ := h_img_sub h4
    exact (Set.Finite.mem_toFinset).mpr h5
  have h4 : h_preimg_fin.toFinset.card ≤ h_S_fin.toFinset.card := by rw [h2]; exact Finset.card_le_card h3
  have h_union_fin : (Upper ∪ Lower).Finite := Set.Finite.union h_upper_fin h_lower_fin
  have h_sub_S : S_ℂ ⊆ Upper ∪ Lower := by
    intro s hs; have him : |s.im| ≤ T := hs.2.2.2
    by_cases h : 0 ≤ s.im
    · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1, h, by linarith [abs_le.mp him]⟩
    · exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1, by linarith [abs_le.mp him], by linarith⟩
  have h5 : h_S_fin.toFinset.card ≤ h_union_fin.toFinset.card := by
    have h51 : h_S_fin.toFinset ⊆ h_union_fin.toFinset := by
      intro z hz; have h6 : z ∈ S_ℂ := (Set.Finite.mem_toFinset).mp hz
      have h7 : z ∈ Upper ∪ Lower := h_sub_S h6
      exact (Set.Finite.mem_toFinset).mpr h7
    exact Finset.card_le_card h51
  have h_eq_union : h_union_fin.toFinset = h_upper_fin.toFinset ∪ h_lower_fin.toFinset :=
    Set.Finite.toFinset_union h_upper_fin h_lower_fin h_union_fin
  have h6 : h_union_fin.toFinset.card ≤ h_upper_fin.toFinset.card + h_lower_fin.toFinset.card := by
    rw [h_eq_union]; exact Finset.card_union_le _ _
  have h_star_img_fin2 : (star '' Lower).Finite := h_star_img_fin
  have h_eq_star : h_star_img_fin2.toFinset = Finset.image star h_lower_fin.toFinset :=
    Set.Finite.toFinset_image star h_lower_fin h_star_img_fin2
  have h7 : h_lower_fin.toFinset.card = h_star_img_fin2.toFinset.card := by
    rw [h_eq_star, Finset.card_image_of_injOn] <;> exact fun x _ y _ hxy => star_inj x y hxy
  have h8 : h_star_img_fin2.toFinset = h_upper_fin.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset]
    have h9 : z ∈ star '' Lower ↔ z ∈ Upper := by rw [h_eq_lower_upper]
    exact h9
  have h9 : h_lower_fin.toFinset.card = h_upper_fin.toFinset.card := by rw [h7, h8]
  have h10 : h_upper_fin.toFinset.card ≤ Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) :=
    card_le_of_encard_le h_upper_fin h_upper_encard
  have h_log_pos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have h_nonneg : 0 ≤ C1 * (T + 1) * Real.log (T + 2) := by positivity
  have h11 : (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ℝ) ≤ C1 * (T + 1) * Real.log (T + 2) + 1 :=
    ceil_le_add_one (C1 * (T + 1) * Real.log (T + 2)) h_nonneg
  calc (h_layer_fin.toFinset.card : ℝ)
    ≤ (h_preimg_fin.toFinset.card : ℝ) := by exact_mod_cast h1
    _ ≤ (h_S_fin.toFinset.card : ℝ) := by exact_mod_cast h4
    _ ≤ (h_union_fin.toFinset.card : ℝ) := by exact_mod_cast h5
    _ ≤ (h_upper_fin.toFinset.card : ℝ) + (h_lower_fin.toFinset.card : ℝ) := by exact_mod_cast h6
    _ = 2 * (h_upper_fin.toFinset.card : ℝ) := by rw [h9] <;> ring
    _ ≤ 2 * (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ℝ) := by gcongr
    _ ≤ 2 * (C1 * (T + 1) * Real.log (T + 2) + 1) := by gcongr

#check layer_card_bound_raw

end RHSpectralDuality
