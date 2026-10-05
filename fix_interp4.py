path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old = """/-- 有限和单点修改引理（sorry，标准有限和性质）：
    若 f 与 f0 只在 l0 处不同，则 Σ w(ℓ)·f(ℓ) = Σ w(ℓ)·f0(ℓ) + w(l0)·(f(l0)-f0(l0))。 -/
axiom finite_sum_single_point_change (s : Finset ℝ) (l0 : ℝ) (hl0 : l0 ∈ s)
    (f f0 : ℝ → ℂ) (h : ∀ x ∈ s, x ≠ l0 → f x = f0 x) :
    ∑ x ∈ s, f x = (∑ x ∈ s, f0 x) + (f l0 - f0 l0)"""

new = """/-- 有限和单点修改引理（定理，标准有限和性质）： -/
theorem finite_sum_single_point_change (s : Finset ℝ) (l0 : ℝ) (hl0 : l0 ∈ s)
    (f f0 : ℝ → ℂ) (h : ∀ x ∈ s, x ≠ l0 → f x = f0 x) :
    ∑ x ∈ s, f x = (∑ x ∈ s, f0 x) + (f l0 - f0 l0) := by
  have h1 : ∑ x ∈ s, f x = ∑ x ∈ s.erase l0, f x + f l0 := by
    rw [Finset.sum_erase_add hl0 f] <;> abel
  have h2 : ∑ x ∈ s, f0 x = ∑ x ∈ s.erase l0, f0 x + f0 l0 := by
    rw [Finset.sum_erase_add hl0 f0] <;> abel
  have h3 : ∑ x ∈ s.erase l0, f x = ∑ x ∈ s.erase l0, f0 x := by
    apply Finset.sum_congr rfl
    intro x hx
    have h4 : x ≠ l0 := (Finset.mem_erase.mp hx).1
    have h5 : x ∈ s := (Finset.mem_erase.mp hx).2
    exact h x h5 h4
  rw [h1, h2, h3] <;> abel"""

content = content.replace(old, new)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Downgraded finite_sum_single_point_change to theorem')
