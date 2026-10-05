with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old_proof = '''  rcases mellin_finite_surjectivity_zero_sum_norm_bound with ⟨C, hC_pos, h_main⟩
  let s_T : Finset ℂ := hT.toFinset
  let B : ℝ := s_T.sup (fun t => ‖w t‖)
  have hB : ∀ (t : ℂ), t ∈ T → ‖w t‖ ≤ B := by
    intro t ht
    have h_in : t ∈ s_T := hT.mem_toFinset.mpr ht
    exact Finset.le_sup h_in
  rcases h_main T hT w B hB with ⟨h, hh, h_nz, _⟩
  exact ⟨h, hh, h_nz⟩'''

new_proof = '''  rcases mellin_finite_surjectivity_zero_sum_norm_bound with ⟨C, hC_pos, h_main⟩
  have h_image_finite : (Set.image w T).Finite := Set.Finite.image w hT
  have h_norm_image_finite : (Set.image (fun t : ℂ => ‖w t‖) T).Finite := Set.Finite.image (fun t : ℂ => ‖w t‖) hT
  have h_bdd : ∃ (B : ℝ), ∀ (t : ℂ), t ∈ T → ‖w t‖ ≤ B := by
    have h1 : (Set.image (fun t : ℂ => ‖w t‖) T).Finite := h_norm_image_finite
    have h2 : ∃ (B : ℝ), ∀ (x : ℝ), x ∈ Set.image (fun t : ℂ => ‖w t‖) T → x ≤ B := by
      exact Set.Finite.bddAbove h1
    rcases h2 with ⟨B, hB⟩
    refine ⟨max B 0, ?_⟩
    intro t ht
    have h3 : ‖w t‖ ∈ Set.image (fun t : ℂ => ‖w t‖) T := ⟨t, ht, rfl⟩
    have h4 : ‖w t‖ ≤ B := hB ‖w t‖ h3
    exact le_trans h4 (le_max_left B 0)
  rcases h_bdd with ⟨B, hB⟩
  rcases h_main T hT w B hB with ⟨h, hh, h_nz, _⟩
  exact ⟨h, hh, h_nz⟩'''

if old_proof in content:
    content = content.replace(old_proof, new_proof)
    print("证明修复成功")
else:
    print("未找到目标证明")

with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("完成")
