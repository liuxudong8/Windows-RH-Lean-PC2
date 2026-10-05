import OrderPreservingBijection.stage_4

namespace TestCardBound

open RHSpectralDuality

-- 核心引理：单射下，原像有限集的 card ≤ 像集的 card（特化到 ℕ → ℂ）
lemma card_preimage_le_image {s : Set ℕ} {t : Set ℂ}
    (h_inj : Function.Injective nontrivialZeroEnum) (h_sub : nontrivialZeroEnum '' s ⊆ t)
    (h_t_fin : t.Finite) (h_s_fin : s.Finite) :
    h_s_fin.toFinset.card ≤ h_t_fin.toFinset.card := by
  have h_img_fin : (nontrivialZeroEnum '' s).Finite := Set.Finite.subset h_t_fin h_sub
  have h1 : h_img_fin.toFinset = Finset.image nontrivialZeroEnum h_s_fin.toFinset :=
    Set.Finite.toFinset_image nontrivialZeroEnum h_s_fin h_img_fin
  have h2 : h_s_fin.toFinset.card = h_img_fin.toFinset.card := by
    rw [h1, Finset.card_image_of_injOn]
    <;> exact fun x _ y _ hxy => h_inj hxy
  rw [h2]
  have h3 : h_img_fin.toFinset ⊆ h_t_fin.toFinset := by
    exact Set.Finite.toFinset_subset.mpr (Set.Subset.trans h_sub (by simp))
  exact Finset.card_le_card h3

-- 核心引理：Upper ∪ Lower 的 card ≤ 2 * card(Upper)
lemma card_union_le_double (Upper Lower : Set ℂ) (h_upper_fin : Upper.Finite) (h_lower_fin : Lower.Finite)
    (h_eq_card : h_lower_fin.toFinset.card = h_upper_fin.toFinset.card) :
    (Set.Finite.union h_upper_fin h_lower_fin).toFinset.card ≤ 2 * h_upper_fin.toFinset.card := by
  have h_union_fin : (Upper ∪ Lower).Finite := Set.Finite.union h_upper_fin h_lower_fin
  have h1 : h_union_fin.toFinset = h_upper_fin.toFinset ∪ h_lower_fin.toFinset :=
    Set.Finite.toFinset_union h_upper_fin h_lower_fin h_union_fin
  rw [h1]
  have h2 : (h_upper_fin.toFinset ∪ h_lower_fin.toFinset).card ≤ h_upper_fin.toFinset.card + h_lower_fin.toFinset.card :=
    Finset.card_union_le _ _
  rw [h_eq_card] at h2
  linarith

#check card_preimage_le_image
#check card_union_le_double

end TestCardBound
