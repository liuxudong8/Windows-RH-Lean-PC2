f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- 消零子空间中成对和非零存在性（公理，插值理论）：
    如果消零子空间非空，则存在消零函数 g₀ 使得成对和 ≠ 0。

    数学依据：消零约束定义了一个线性子空间，成对和映射是该子空间上的线性泛函。
    若该子空间非平凡，则成对和映射不恒为零（否则子空间被额外约束，与非平凡矛盾）。
    风险等级：中低（非零泛函的存在性，比满射性弱）。 -/
axiom vanishing_subspace_pair_sum_nonzero_exists (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    (∃ (g0 : MollifiedTestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform g0.toTestFunction ρ' = 0) ∧
      (∀ (k : ℕ), melinTransform g0.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
      melinTransform g0.toTestFunction (1 : ℂ) = 0) →
    ∃ (g0 : MollifiedTestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform g0.toTestFunction ρ' = 0) ∧
      (∀ (k : ℕ), melinTransform g0.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
      melinTransform g0.toTestFunction (1 : ℂ) = 0 ∧
      (melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) ≠ 0)"""

new = """/-- 消零子空间中成对和非零存在性（定理，由可数集任意赋值推出）：
    如果消零子空间非空，则存在消零函数 g₀ 使得成对和 ≠ 0。

    证明：令 S = (所有零点∪极点) ∪ {ρ, 1-ρ}，可数。
    取赋值 v(ρ)=1, v(s)=0（s≠ρ），由 mellin_countable_interpolation 存在 g₀。
    则 M[g₀](ρ)+M[g₀](1-ρ) = 1（若 ρ≠1-ρ）或 2（若 ρ=1-ρ），均 ≠ 0。
    前提中的"存在 g₀"实际上冗余（结论只依赖插值公理）。 -/
theorem vanishing_subspace_pair_sum_nonzero_exists (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    (∃ (g0 : MollifiedTestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform g0.toTestFunction ρ' = 0) ∧
      (∀ (k : ℕ), melinTransform g0.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
      melinTransform g0.toTestFunction (1 : ℂ) = 0) →
    ∃ (g0 : MollifiedTestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform g0.toTestFunction ρ' = 0) ∧
      (∀ (k : ℕ), melinTransform g0.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
      melinTransform g0.toTestFunction (1 : ℂ) = 0 ∧
      (melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) ≠ 0) := by
  intro hz hre1 hre2 _
  let S_nontriv : Set ℂ := {ρ' | _root_.riemannZeta ρ' = 0 ∧ 0 < ρ'.re ∧ ρ'.re < 1}
  let S_triv : Set ℂ := Set.range (fun k : ℕ => ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) ∪ {1}
  let S : Set ℂ := S_nontriv ∪ S_triv ∪ {ρ, 1 - ρ}
  have h_nontriv_count : S_nontriv.Countable := by
    have h_sub : S_nontriv ⊆ Set.range nontrivialZeroEnum := by
      intro ρ' h
      have h1 : _root_.riemannZeta ρ' = 0 := h.1
      have h2 : 0 < ρ'.re := h.2.1
      have h3 : ρ'.re < 1 := h.2.2
      have h4 : ∃ (n : ℕ), nontrivialZeroEnum n = ρ' := nontrivialZeroEnum_covers_all ρ' h1 h2 h3
      exact h4
    exact Set.Countable.mono h_sub (Set.countable_range nontrivialZeroEnum)
  have h_triv_count : S_triv.Countable := Set.Countable.union (Set.countable_range _) (Set.countable_singleton _)
  have hS_count : S.Countable := by
    simp [S]
    <;> exact Set.Countable.union (Set.Countable.union h_nontriv_count h_triv_count) (Set.countable_insert _ (Set.countable_singleton _))
  let v : ℂ → ℂ := fun s => if s = ρ then 1 else 0
  rcases mellin_countable_interpolation S hS_count v with ⟨g0, hg0⟩
  refine' ⟨g0, _⟩
  have h_rho : melinTransform g0.toTestFunction ρ = 1 := by
    rw [hg0 ρ (Or.inr (Or.inr (Or.inl (Set.mem_singleton _))))]
    <;> simp [v]
  have h_pair : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) ≠ 0 := by
    by_cases h_eq : ρ = 1 - ρ
    · subst h_eq
      rw [h_rho, h_rho] <;> norm_num
    · have h_1mrho : melinTransform g0.toTestFunction (1 - ρ) = 0 := by
        rw [hg0 (1 - ρ) (Or.inr (Or.inr (Or.inr (Set.mem_singleton _))))]
        <;> simp [v, h_eq]
      rw [h_rho, h_1mrho] <;> norm_num
  constructor
  · intro ρ' hz' hre1' hre2' hne1 hne2
    exact hg0 ρ' (Or.inl ⟨hz', hre1', hre2'⟩)
  · constructor
    · intro k
      exact hg0 ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) (Or.inr (Or.inl (Or.inl (Set.mem_range_self k))))
    · constructor
      · exact hg0 (1 : ℂ) (Or.inr (Or.inl (Or.inr (Set.mem_singleton _))))
      · exact h_pair"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: vanishing_subspace_pair_sum_nonzero_exists -> theorem')
