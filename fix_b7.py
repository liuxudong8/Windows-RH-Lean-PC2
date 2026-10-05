f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """  intro _ _
  let S : Set ℝ := Set.range specDiscM
  have hS_count : S.Countable := Set.countable_range _
  exact mellin_shift_preserving_spectral_values f g S hS_count"""

new = """  intro _ _
  let S : Set ℝ := Set.range specDiscM
  have hS_count : S.Countable := Set.countable_range _
  rcases mellin_shift_preserving_spectral_values f g S hS_count with ⟨f', h_melin, h_spec⟩
  refine' ⟨f', _⟩
  constructor
  · intro n
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    exact h_spec (specDiscM n) h_in
  · exact h_melin"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: fixed spectral_base_invariance proof')
