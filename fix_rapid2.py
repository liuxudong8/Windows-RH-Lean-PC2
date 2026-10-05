with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 mellin_rapid_decay_choice 的起始和结束
start_idx = None
end_idx = None
for i, line in enumerate(lines):
    if 'theorem mellin_rapid_decay_choice' in line:
        start_idx = i
    if start_idx is not None and i > start_idx and line.strip() == '' and lines[i+1].strip().startswith('/--'):
        end_idx = i
        break

print(f"start={start_idx+1}, end={end_idx+1}")

new_theorem = '''/-- 速降插值选择定理（由光滑插值 + C² 速降估计推出）：
    对非临界线零点 ρ 和目标值 wρ，对任意有限 T（ρ∉T），
    存在常数 C(T) 和磨光函数 h 满足零谱点插值条件且 Mellin 变换速降。
    注：C(T) 依赖于 T（因为对偶范数界 C(s) 依赖于 s），但对每个固定 T 有限。 -/
theorem mellin_rapid_decay_choice (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (C : ℝ), 0 < C ∧
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * max ‖wρ‖ 1 / (1 + |s.im|) ^ 2) := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_smooth_interpolation ρ wρ hz hre1 hre2 hne T hT hρ_notin with ⟨B, hB_pos, h, h_spec, h_mel_ρ, h_mel_T, hC2, h_deriv_bound⟩
  let C := B + 1
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, h, h_spec, h_mel_ρ, h_mel_T, ?_⟩
  intro s hs_re1 hs_re2
  have h_decay : ‖melinTransform h.toTestFunction s‖ ≤ (B * max ‖wρ‖ 1 + 1) / (1 + |s.im|) ^ 2 :=
    mellin_transform_C2_rapid_decay h.toTestFunction (B * max ‖wρ‖ 1) hC2 h_deriv_bound (by positivity) s hs_re1 hs_re2
  have h_final : (B * max ‖wρ‖ 1 + 1) / (1 + |s.im|) ^ 2 ≤ C * max ‖wρ‖ 1 / (1 + |s.im|) ^ 2 := by
    have h1 : 1 ≤ max ‖wρ‖ 1 := by apply le_max_right
    have h2 : B * max ‖wρ‖ 1 + 1 ≤ C * max ‖wρ‖ 1 := by
      dsimp only [C]
      have h3 : B * max ‖wρ‖ 1 + 1 ≤ (B + 1) * max ‖wρ‖ 1 := by
        have h4 : 1 ≤ max ‖wρ‖ 1 := h1
        nlinarith
      exact h3
    gcongr
    <;> linarith
  exact le_trans h_decay h_final

'''.split('\n')

lines[start_idx:end_idx+1] = [l + '\n' for l in new_theorem]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('done')
