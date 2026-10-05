import OrderPreservingBijection.stage_4

namespace TestLayerCard

open RHSpectralDuality

-- 从 stage_4 导入基础设施引理
#check @card_le_of_encard_le
#check @lower_conj_eq_upper
#check @finite_of_encard_le

-- layer 定义
let layer (k : ℕ) : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}

-- h_card_bound 核心引理（直接上界，不简化系数）
lemma layer_card_bound_raw (C1 : ℝ) (hC1_pos : 0 < C1)
    (hC1 : ∀ (T : ℝ), 0 < T → Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat))
    (k : ℕ) (h_layer_fin : (layer k).Finite) :
    (h_layer_fin.toFinset.card : ℝ) ≤ 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) := by
  let T := (2^(k+1) : ℝ)
  have hT_pos : 0 < T := by positivity
  let Upper : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
  let Lower : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0}
  let S_ℂ : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T}
  let preimage : Set ℕ := {n | |(nontrivialZeroEnum n).im| ≤ T}
  have h_upper_encard : Set.encard Upper ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat) := hC1 T hT_pos
  have h_upper_fin : Upper.Finite := finite_of_encard_le h_upper_encard
  have h_lower_fin : Lower.Finite := by
    have h_eq : star '' Lower = Upper := lower_conj_eq_upper T
    have h : (star '' Lower).Finite := Set.Finite.image _ h_upper_fin
    rw [h_eq] at h; exact h
  have h_S_fin : S_ℂ.Finite := by
    have h_decomp : S_ℂ ⊆ Upper ∪ Lower := by
      intro s hs; have him : |s.im| ≤ T := hs.2.2.2
      by_cases h : 0 ≤ s.im
      · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1, h, by linarith [abs_le.mp him]⟩
      · exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1, by linarith [abs_le.mp him], by linarith⟩
    exact Set.Finite.subset (Set.Finite.union h_upper_fin h_lower_fin) h_decomp
  have h_img_sub : nontrivialZeroEnum '' preimage ⊆ S_ℂ := by
    intro s hs; rcases hs with ⟨n, _, rfl⟩
    exact ⟨(nontrivialZeroEnum_are_zeros n).1, (nontrivialZeroEnum_are_zeros n).2.1, (nontrivialZeroEnum_are_zeros n).2.2, by tauto⟩
  have h_preimg_fin : preimage.Finite := by
    have h_img_fin : (nontrivialZeroEnum '' preimage).Finite := Set.Finite.subset h_S_fin h_img_sub
    exact finite_preimage_of_injective nontrivialZeroEnum_injective h_img_fin
  have h1 : h_layer_fin.toFinset.card ≤ h_preimg_fin.toFinset.card := by
    apply Finset.card_le_card
    exact Set.Finite.toFinset_subset.mpr (show layer k ⊆ preimage from fun n hn => le_of_lt hn.2)
  have h2 : h_preimg_fin.toFinset.card ≤ h_S_fin.toFinset.card := by
    have h_img_fin : (nontrivialZeroEnum '' preimage).Finite := Set.Finite.subset h_S_fin h_img_sub
    have h_eq : h_img_fin.toFinset = Finset.image nontrivialZeroEnum h_preimg_fin.toFinset :=
      Set.Finite.toFinset_image nontrivialZeroEnum h_preimg_fin h_img_fin
    have h3 : h_preimg_fin.toFinset.card = h_img_fin.toFinset.card := by
      rw [h_eq, Finset.card_image_of_injOn] <;> exact fun x _ y _ hxy => nontrivialZeroEnum_injective hxy
    rw [h3]
    exact Finset.card_le_card (Set.Finite.toFinset_subset.mpr h_img_sub)
  have h_union_fin : (Upper ∪ Lower).Finite := Set.Finite.union h_upper_fin h_lower_fin
  have h4 : h_S_fin.toFinset.card ≤ h_union_fin.toFinset.card := by
    apply Finset.card_le_card
    exact Set.Finite.toFinset_subset.mpr (show S_ℂ ⊆ Upper ∪ Lower from by
      intro s hs; have him : |s.im| ≤ T := hs.2.2.2
      by_cases h : 0 ≤ s.im
      · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1, h, by linarith [abs_le.mp him]⟩
      · exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1, by linarith [abs_le.mp him], by linarith⟩)
  have h5 : h_union_fin.toFinset.card ≤ h_upper_fin.toFinset.card + h_lower_fin.toFinset.card := by
    have h_eq : h_union_fin.toFinset = h_upper_fin.toFinset ∪ h_lower_fin.toFinset :=
      Set.Finite.toFinset_union h_upper_fin h_lower_fin h_union_fin
    rw [h_eq]
    exact Finset.card_union_le _ _
  have h6 : h_lower_fin.toFinset.card = h_upper_fin.toFinset.card := by
    have h_eq : star '' Lower = Upper := lower_conj_eq_upper T
    have h_img_fin : (star '' Lower).Finite := Set.Finite.image _ h_lower_fin
    have h7 : h_img_fin.toFinset = Finset.image star h_lower_fin.toFinset :=
      Set.Finite.toFinset_image star h_lower_fin h_img_fin
    have h8 : h_lower_fin.toFinset.card = h_img_fin.toFinset.card := by
      rw [h7, Finset.card_image_of_injOn] <;> exact fun x _ y _ hxy => by simpa using hxy
    rw [h8, h_eq]
    <;> rfl
  have h7 : h_upper_fin.toFinset.card ≤ Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) :=
    card_le_of_encard_le h_upper_fin h_upper_encard
  calc (h_layer_fin.toFinset.card : ℝ)
    ≤ (h_preimg_fin.toFinset.card : ℝ) := by exact_mod_cast h1
    _ ≤ (h_S_fin.toFinset.card : ℝ) := by exact_mod_cast h2
    _ ≤ (h_union_fin.toFinset.card : ℝ) := by exact_mod_cast h4
    _ ≤ (h_upper_fin.toFinset.card : ℝ) + (h_lower_fin.toFinset.card : ℝ) := by exact_mod_cast h5
    _ = 2 * (h_upper_fin.toFinset.card : ℝ) := by rw [h6] <;> ring
    _ ≤ 2 * (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ℝ) := by gcongr
    _ ≤ 2 * (C1 * (T + 1) * Real.log (T + 2) + 1) := by
      have h9 : (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ℝ) ≤ C1 * (T + 1) * Real.log (T + 2) + 1 := by
        exact Nat.ceil_le.mpr (by linarith)
      gcongr

#check layer_card_bound_raw

end TestLayerCard
