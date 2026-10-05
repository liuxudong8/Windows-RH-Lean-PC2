f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 错误1: simpa [w] using h -> ring 证明
content = content.replace(
    "    have h : melinTransform f'.toTestFunction s = w s := h_melin s hs\n    simpa [w] using h",
    "    have h : melinTransform f'.toTestFunction s = w s := h_melin s hs\n    have h' : melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =\n              melinTransform g.toTestFunction s := by\n      rw [h, w]\n      ring\n    exact h'"
)

# 错误2: spectral_values_preserving_melin_vanishing 中 hn.symm -> hn
content = content.replace(
    "      have h_in_nontriv : ρ ∈ nontrivSet := ⟨n, hn.symm⟩",
    "      have h_in_nontriv : ρ ∈ nontrivSet := ⟨n, hn⟩"
)

# 错误3: spectral_preserving_perturbation_build 中 h_in_T 的 Or.inl 分支
content = content.replace(
    "    · rcases h with ⟨n, hn⟩; exact Or.inl (Or.inl ⟨n, hn.symm⟩)",
    "    · rcases h with ⟨n, hn⟩; exact Or.inl (Or.inl ⟨n, hn⟩)"
)

# 错误4: hk -> hk.symm
content = content.replace(
    "    · rcases h with ⟨k, hk⟩; exact Or.inl (Or.inr ⟨k, hk⟩)",
    "    · rcases h with ⟨k, hk⟩; exact Or.inl (Or.inr ⟨k, hk.symm⟩)"
)

# 错误5: h_pts 方向 - 在 spectral_preserving_perturbation_build 的 exact 中
# h_pts : ∀ n, f2.eval = f1.eval, 需要 ∀ n, f1.eval = f2.eval
content = content.replace(
    "  exact ⟨f1, f2, h_pts, h_other, h_pair_diff, h_triv_eq⟩",
    "  have h_pts' : ∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) := by\n    intro n; exact (h_pts n).symm\n  exact ⟨f1, f2, h_pts', h_other, h_pair_diff, h_triv_eq⟩"
)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('All 5 fixes applied')
