f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- 保持谱点取值的 Mellin 全局消零能力（定理，由全局反符号核+谱点保持叠加推出）：
    对任意磨光函数 f，存在另一个磨光函数 f' 满足：
    (1) 保持谱点取值：f'.eval(specDiscM k) = f.eval(specDiscM k) 对所有 k
    (2) Mellin 全局消零：对所有非平凡零点 ρ，melinTransform f' ρ = 0
    (3) Mellin 全局消零：对所有平凡零点 s=-2k，melinTransform f' (-2k) = 0
    (4) Mellin 全局消零：在极点 s=1 处，melinTransform f' 1 = 0

    证明：
    (1) melin_transform_global_vanishing(f) 给出 g，使得 M[g] = -M[f] 在零点和极点处
    (2) spectral_preserving_melin_superposition_from(f, g) 给出 f'，
        保持谱点取值且 M[f'] - M[f] = M[g]
    (3) 因此 M[f'] = M[f] + M[g] = M[f] - M[f] = 0 在零点和极点处 -/
theorem spectral_values_preserving_melin_vanishing :
    ∀ (f : MollifiedTestFunction),
      ∃ (f' : MollifiedTestFunction),
        (∀ (k : ℕ), f'.toTestFunction.eval (specDiscM k) = f.toTestFunction.eval (specDiscM k)) ∧
        (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
          melinTransform f'.toTestFunction ρ = 0) ∧
        (∀ (k : ℕ), melinTransform f'.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
        melinTransform f'.toTestFunction (1 : ℂ) = 0 := by
  intro f
  rcases melin_transform_global_vanishing f with ⟨g, h_nontriv_neg, h_triv_neg, h_pole_neg⟩
  rcases spectral_preserving_melin_superposition_from f g with ⟨f', h_pts, h_diff⟩
  have h_nontriv_zero : ∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      melinTransform f'.toTestFunction ρ = 0 := by
    intro ρ hz hre1 hre2
    have h : melinTransform f'.toTestFunction ρ - melinTransform f.toTestFunction ρ =
             -melinTransform f.toTestFunction ρ := by
      rw [h_diff ρ, h_nontriv_neg ρ hz hre1 hre2]
    calc
      melinTransform f'.toTestFunction ρ
        = melinTransform f.toTestFunction ρ + (melinTransform f'.toTestFunction ρ - melinTransform f.toTestFunction ρ) := by ring
      _ = melinTransform f.toTestFunction ρ + (-melinTransform f.toTestFunction ρ) := by rw [h]
      _ = 0 := by ring
  have h_triv_zero : ∀ (k : ℕ), melinTransform f'.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0 := by
    intro k
    let s : ℂ := ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)
    have h : melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
             -melinTransform f.toTestFunction s := by
      rw [h_diff s, h_triv_neg k]
    calc
      melinTransform f'.toTestFunction s
        = melinTransform f.toTestFunction s + (melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s) := by ring
      _ = melinTransform f.toTestFunction s + (-melinTransform f.toTestFunction s) := by rw [h]
      _ = 0 := by ring
  have h_pole_zero : melinTransform f'.toTestFunction (1 : ℂ) = 0 := by
    have h : melinTransform f'.toTestFunction (1 : ℂ) - melinTransform f.toTestFunction (1 : ℂ) =
             -melinTransform f.toTestFunction (1 : ℂ) := by
      rw [h_diff (1 : ℂ), h_pole_neg]
    calc
      melinTransform f'.toTestFunction (1 : ℂ)
        = melinTransform f.toTestFunction (1 : ℂ) + (melinTransform f'.toTestFunction (1 : ℂ) - melinTransform f.toTestFunction (1 : ℂ)) := by ring
      _ = melinTransform f.toTestFunction (1 : ℂ) + (-melinTransform f.toTestFunction (1 : ℂ)) := by rw [h]
      _ = 0 := by ring
  exact ⟨f', h_pts, h_nontriv_zero, h_triv_zero, h_pole_zero⟩"""

new = """/-- 保持谱点取值的 Mellin 消零能力（定理，由反符号核+可数点集叠加推出）：
    对任意磨光函数 f，存在另一个磨光函数 f' 满足：
    (1) 保持谱点取值：f'.eval(specDiscM k) = f.eval(specDiscM k) 对所有 k
    (2) Mellin 消零：对所有非平凡零点 ρ，melinTransform f' ρ = 0
    (3) Mellin 消零：对所有平凡零点 s=-2k，melinTransform f' (-2k) = 0
    (4) Mellin 消零：在极点 s=1 处，melinTransform f' 1 = 0

    证明：
    (1) melin_transform_global_vanishing(f) 给出 g，使得 M[g] = -M[f] 在零点和极点处
    (2) spectral_preserving_melin_superposition_countable(f, g, T) 给出 f'，
        保持谱点取值且 M[f'] - M[f] = M[g] 在可数集 T = 零点∪平凡零点∪{1} 上
    (3) 因此 M[f'] = M[f] + M[g] = 0 在零点和极点处 -/
theorem spectral_values_preserving_melin_vanishing :
    ∀ (f : MollifiedTestFunction),
      ∃ (f' : MollifiedTestFunction),
        (∀ (k : ℕ), f'.toTestFunction.eval (specDiscM k) = f.toTestFunction.eval (specDiscM k)) ∧
        (∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
          melinTransform f'.toTestFunction ρ = 0) ∧
        (∀ (k : ℕ), melinTransform f'.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
        melinTransform f'.toTestFunction (1 : ℂ) = 0 := by
  intro f
  rcases melin_transform_global_vanishing f with ⟨g, h_nontriv_neg, h_triv_neg, h_pole_neg⟩
  let nontrivSet : Set ℂ := Set.range nontrivialZeroEnum
  let trivSet : Set ℂ := Set.range (fun k : ℕ => ((-2 * (k + 1 : ℕ) : ℝ) : ℂ))
  let T : Set ℂ := nontrivSet ∪ trivSet ∪ {1}
  have hT_count : T.Countable := by
    apply Set.Countable.union
    · apply Set.Countable.union
      · exact Set.countable_range _
      · exact Set.countable_range _
    · exact Set.countable_singleton _
  rcases spectral_preserving_melin_superposition_countable f g T hT_count with ⟨f', h_pts, h_diff⟩
  have h_nontriv_zero : ∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      melinTransform f'.toTestFunction ρ = 0 := by
    intro ρ hz hre1 hre2
    have hρ_in_T : ρ ∈ T := by
      have h_exists : ∃ n : ℕ, nontrivialZeroEnum n = ρ := nontrivialZeroEnum_covers_all ρ hz hre1 hre2
      rcases h_exists with ⟨n, hn⟩
      have h_in_nontriv : ρ ∈ nontrivSet := ⟨n, hn.symm⟩
      exact Or.inl (Or.inl h_in_nontriv)
    have h : melinTransform f'.toTestFunction ρ - melinTransform f.toTestFunction ρ =
             -melinTransform f.toTestFunction ρ := by
      rw [h_diff ρ hρ_in_T, h_nontriv_neg ρ hz hre1 hre2]
    calc
      melinTransform f'.toTestFunction ρ
        = melinTransform f.toTestFunction ρ + (melinTransform f'.toTestFunction ρ - melinTransform f.toTestFunction ρ) := by ring
      _ = melinTransform f.toTestFunction ρ + (-melinTransform f.toTestFunction ρ) := by rw [h]
      _ = 0 := by ring
  have h_triv_zero : ∀ (k : ℕ), melinTransform f'.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0 := by
    intro k
    let s : ℂ := ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)
    have hs_in_T : s ∈ T := by
      have h_in_triv : s ∈ trivSet := ⟨k, rfl⟩
      exact Or.inl (Or.inr h_in_triv)
    have h : melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s =
             -melinTransform f.toTestFunction s := by
      rw [h_diff s hs_in_T, h_triv_neg k]
    calc
      melinTransform f'.toTestFunction s
        = melinTransform f.toTestFunction s + (melinTransform f'.toTestFunction s - melinTransform f.toTestFunction s) := by ring
      _ = melinTransform f.toTestFunction s + (-melinTransform f.toTestFunction s) := by rw [h]
      _ = 0 := by ring
  have h_pole_zero : melinTransform f'.toTestFunction (1 : ℂ) = 0 := by
    have h1_in_T : (1 : ℂ) ∈ T := Or.inr (Set.mem_singleton _)
    have h : melinTransform f'.toTestFunction (1 : ℂ) - melinTransform f.toTestFunction (1 : ℂ) =
             -melinTransform f.toTestFunction (1 : ℂ) := by
      rw [h_diff (1 : ℂ) h1_in_T, h_pole_neg]
    calc
      melinTransform f'.toTestFunction (1 : ℂ)
        = melinTransform f.toTestFunction (1 : ℂ) + (melinTransform f'.toTestFunction (1 : ℂ) - melinTransform f.toTestFunction (1 : ℂ)) := by ring
      _ = melinTransform f.toTestFunction (1 : ℂ) + (-melinTransform f.toTestFunction (1 : ℂ)) := by rw [h]
      _ = 0 := by ring
  exact ⟨f', h_pts, h_nontriv_zero, h_triv_zero, h_pole_zero⟩"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Step 3a done: spectral_values_preserving_melin_vanishing uses countable version')
