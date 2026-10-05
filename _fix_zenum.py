from pathlib import Path

p = Path(r"c:\proj2\OrderPreservingBijection\ZetaZeros.lean")
t = p.read_text(encoding="utf-8")

# Remove duplicate docstring (lines 14-15)
old_dup = """/-- 非平凡零点枚举的存在性（定理）：临界带内非平凡零点集可数
    （mathlib `isDiscrete_riemannZetaZeros` + 紧集有限），故存在单射枚举。 -/
"""
t = t.replace(old_dup, "", 1)

# Fix isCompact_closedBall: need N as ℝ
t = t.replace(
    "have h_comp : IsCompact (Metric.closedBall (0:ℂ) N) := isCompact_closedBall",
    "have h_comp : IsCompact (Metric.closedBall (0:ℂ) (N:ℝ)) := isCompact_closedBall"
)
# Fix hsub
t = t.replace(
    """      have hsub : (S ∩ Metric.closedBall (0:ℂ) N) ⊆ (Metric.closedBall (0:ℂ) N ∩ riemannZetaZeros) := by
        intro z hz; exact ⟨hz.2, hz.1⟩""",
    """      have hsub : (S ∩ Metric.closedBall (0:ℂ) (N:ℝ)) ⊆ (Metric.closedBall (0:ℂ) (N:ℝ) ∩ riemannZetaZeros) := by
        intro z hz; exact ⟨hz.2, hz.1.1⟩"""
)
# Fix h1 type
t = t.replace(
    "have h1 : ∀ (N : ℕ), (S ∩ Metric.closedBall (0:ℂ) N).Finite := by",
    "have h1 : ∀ (N : ℕ), (S ∩ Metric.closedBall (0:ℂ) (N:ℝ)).Finite := by"
)
# Fix h2 union
t = t.replace(
    "have h2 : S = ⋃ (N : ℕ), (S ∩ Metric.closedBall (0:ℂ) N) := by",
    "have h2 : S = ⋃ (N : ℕ), (S ∩ Metric.closedBall (0:ℂ) (N:ℝ)) := by"
)

p.write_text(t, encoding="utf-8")
print("done")
