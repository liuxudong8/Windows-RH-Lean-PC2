path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Fix 1: noncomputable + linarith
old1 = """def intervalIndicator (a b : ℝ) (ha : 0 < a) (hab : a < b) : TestFunction :=
  { toFun := fun x : ℝ => if a ≤ x ∧ x ≤ b then (1 : ℂ) else 0
    hasCompactSupport := by
      refine ⟨b + 1, by linarith, ?_⟩
      intro x hx
      have h_gt_b : x > b := by
        by_cases hpos : 0 ≤ x
        · rw [abs_of_nonneg hpos] at hx; linarith
        · have h_neg : x < 0 := by linarith
          linarith
      have h_notin : ¬(a ≤ x ∧ x ≤ b) := by
        intro h; linarith [h.2]
      simp only [h_notin, if_false] }"""

new1 = """noncomputable def intervalIndicator (a b : ℝ) (ha : 0 < a) (hab : a < b) : TestFunction :=
  { toFun := fun x : ℝ => if a ≤ x ∧ x ≤ b then (1 : ℂ) else 0
    hasCompactSupport := by
      refine ⟨b + 1, by linarith, ?_⟩
      intro x hx
      have h_notin : ¬(a ≤ x ∧ x ≤ b) := by
        by_cases hpos : 0 ≤ x
        · have h_gt : x > b := by rw [abs_of_nonneg hpos] at hx; linarith
          intro h; linarith [h.2]
        · have h_neg : x < 0 := by linarith
          intro h; have h1 : 0 ≤ x := le_of_lt (lt_of_lt_of_le ha h.1); linarith
      simp only [h_notin, if_false] }"""

content = content.replace(old1, new1)

# Fix 2: axiom parameter syntax
old2 = """axiom mellin_interval_linear_independence {m : ℕ} (t : Fin m → ℂ) (ht : Function.Injective t) :
    ∃ (a b : Fin m → ℝ), (∀ i, 0 < a i) ∧ (∀ i, a i < b i) ∧
      ∀ (c : Fin m → ℂ), (∀ j, ∑ i : Fin m, c i * melinTransform (intervalIndicator (a i) (b i) (by exact ‹_›) (by exact ‹_›)) (t j) = 0) → c = 0"""

new2 = """axiom mellin_interval_linear_independence {m : ℕ} (t : Fin m → ℂ) (ht : Function.Injective t) :
    ∃ (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i),
      ∀ (c : Fin m → ℂ), (∀ j, ∑ i : Fin m, c i * melinTransform (intervalIndicator (a i) (b i) (ha i) (hab i)) (t j) = 0) → c = 0"""

content = content.replace(old2, new2)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed 3 errors')
