with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 1. 删除旧注释块（第 2698-2701 行，索引 2697-2700）
# 找到旧注释的起始
for i in range(2690, 2710):
    if '速降插值选择公理（RH 反证法核心' in lines[i]:
        # 删除从这行到下一个 /-- 之前的所有行
        j = i
        while j < len(lines) and not lines[j].strip().startswith('/-- 速降插值选择定理'):
            j += 1
        del lines[i:j]
        print(f"Deleted lines {i+1} to {j}")
        break

# 2. 找到 mellin_pair_uniform_decay_bound 并重写
start_idx = None
end_idx = None
for i, line in enumerate(lines):
    if 'theorem mellin_pair_uniform_decay_bound' in line:
        start_idx = i
    if start_idx is not None and i > start_idx and line.strip() == '' and i+1 < len(lines) and lines[i+1].strip().startswith('/--'):
        end_idx = i
        break

if start_idx is not None and end_idx is not None:
    print(f"Rewriting mellin_pair_uniform_decay_bound at lines {start_idx+1} to {end_idx+1}")
    
    new_theorem = '''/-- Mellin 分离对的速降界（定理，由速降插值选择定理推出）：
    对非临界线零点 ρ，对任意有限 T（ρ∉T），存在常数 C(T) 和磨光函数对 f₁,f₂ 满足速降界。
    证明：用 mellin_rapid_decay_choice 分别构造 h₁(wρ=1) 和 h₂(wρ=0)。 -/
theorem mellin_pair_uniform_decay_bound (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (C : ℝ), 0 < C ∧
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2) := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_rapid_decay_choice ρ (1 : ℂ) hz hre1 hre2 hne T hT hρ_notin with ⟨C1, hC1_pos, h1, h1_spec, h1_mel_ρ, h1_mel_T, h1_decay⟩
  rcases mellin_rapid_decay_choice ρ (0 : ℂ) hz hre1 hre2 hne T hT hρ_notin with ⟨C2, hC2_pos, h2, h2_spec, h2_mel_ρ, h2_mel_T, h2_decay⟩
  let C := 2 * max C1 C2
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, h1, h2, ?_, h1_mel_ρ, h2_mel_ρ, ?_, ?_⟩
  · -- 谱点取值相同（都为 0）
    intro n
    rw [h1_spec n, h2_spec n]
  · -- Mellin 在 T 上相同（都为 0）
    intro s hs
    rw [h1_mel_T s hs, h2_mel_T s hs]
  · -- 速降界
    intro s hs_re1 hs_re2
    have h3 : ‖melinTransform h1.toTestFunction s - melinTransform h2.toTestFunction s‖ ≤
        ‖melinTransform h1.toTestFunction s‖ + ‖melinTransform h2.toTestFunction s‖ := by
      exact norm_sub_le _ _
    have h4 : ‖melinTransform h1.toTestFunction s‖ + ‖melinTransform h2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2 := by
      simp [h1_decay, h2_decay, C] <;> ring_nf <;> norm_num <;> linarith
    exact le_trans h3 h4

'''.split('\n')
    
    lines[start_idx:end_idx+1] = [l + '\n' for l in new_theorem]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('done')
