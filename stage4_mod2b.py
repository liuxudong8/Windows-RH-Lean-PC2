path = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

start_marker = """/-- 可数集上的 Mellin 消零存在性（定理，任意赋值取 v=0 的特例）："""
end_marker = """  exact ⟨f1, f2, h_spec_eq, h_nontriv_ne⟩"""

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)
print(f'start={start_idx}, end={end_idx}')

if start_idx != -1 and end_idx != -1:
    end_idx += len(end_marker)
    new_block = """/-- 非临界线零点的非平凡零点和分离（公理，方向 B 核心，分析断言）：
    对任意非临界线零点 ρ（ρ.re ≠ 1/2），存在两个磨光函数 f₁, f₂，使得：
    (1) 它们在所有谱点 {specDiscM n} 上取值相同
    (2) nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)

    这是方向 B（放弃逐点消零）的核心公理。不要求 M[f](ρ')=0 对所有 ρ'∉{ρ,1-ρ}，
    只要求 nontrivialZeroSum 的差由 {ρ,1-ρ} 主导。
    数学依据：Weil 显式公式 + Mellin 变换插值的自由度，可以构造 f₁,f₂ 使得
    谱侧相同但零点侧的加权和不同。这是反证法的分析核心，待证明。
    风险等级：高（这是 RH 反证法的真正分析核心）。 -/
axiom nontrivial_zero_sum_pair_separation (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        nontrivialZeroSum f1.toTestFunction ≠ nontrivialZeroSum f2.toTestFunction

/-- 非临界线零点的矛盾（定理，由 nontrivial_zero_sum_pair_separation 推出）：
    如果存在非临界线零点 ρ，则存在磨光函数 f 使得
    spectralSum(f) ≠ nontrivialZeroSum(f)。

    证明：由 nontrivial_zero_sum_pair_separation，存在 f₁, f₂ 使得
    谱点取值相同但 nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)。
    由 spectral_sum_determined_by_points，谱点取值相同 ⟹ spectralSum(f₁)=spectralSum(f₂)。
    若 spectralSum(f)=nontrivialZeroSum(f) 对所有磨光 f 成立，则
    nontrivialZeroSum(f₁)=spectralSum(f₁)=spectralSum(f₂)=nontrivialZeroSum(f₂)，矛盾。
    故 f₁, f₂ 中至少有一个满足 spectralSum(f)≠nontrivialZeroSum(f)。 -/
theorem off_critical_line_contradiction :
    ∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f : MollifiedTestFunction),
        spectralSum f.toTestFunction ≠ nontrivialZeroSum f.toTestFunction := by
  intro ρ hz hre1 hre2 hne
  rcases nontrivial_zero_sum_pair_separation ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_nontriv_ne⟩
  have h_spec_eq : spectralSum f1.toTestFunction = spectralSum f2.toTestFunction :=
    spectral_sum_determined_by_points f1.toTestFunction f2.toTestFunction h_pts
  by_cases h1 : spectralSum f1.toTestFunction = nontrivialZeroSum f1.toTestFunction
  · by_cases h2 : spectralSum f2.toTestFunction = nontrivialZeroSum f2.toTestFunction
    · have h_contra : nontrivialZeroSum f1.toTestFunction = nontrivialZeroSum f2.toTestFunction := by
        calc nontrivialZeroSum f1.toTestFunction
          = spectralSum f1.toTestFunction := h1.symm
        _ = spectralSum f2.toTestFunction := h_spec_eq
        _ = nontrivialZeroSum f2.toTestFunction := h2
      exact False.elim (h_nontriv_ne h_contra)
    · exact ⟨f2, h2⟩
  · exact ⟨f1, h1⟩"""

    content = content[:start_idx] + new_block + content[end_idx:]
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print('Stage 2 done')
else:
    print('Markers not found')
