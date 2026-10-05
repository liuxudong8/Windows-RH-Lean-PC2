with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 替换第 2738-2772 行（mellin_rapid_decay_choice）
new_lines = '''/-- 速降插值选择定理（由光滑插值 + C² 速降估计推出）：
    对非临界线零点 ρ 和目标值 wρ，存在 δ > 0 和统一常数 C，使得对任意有限 T（ρ∉T，且 T 中点满足 s.re ≥ δ），
    存在磨光函数 h 满足零谱点插值条件且 Mellin 变换速降。 -/
theorem mellin_rapid_decay_choice (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (δ C : ℝ), 0 < δ ∧ 0 < C ∧ δ ≤ ρ.re ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T → (∀ s ∈ T, δ ≤ s.re) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * max ‖wρ‖ 1 / (1 + |s.im|) ^ 2) := by
  intro hz hre1 hre2 hne
  rcases mellin_smooth_interpolation ρ wρ hz hre1 hre2 hne with ⟨δ, B, hδ_pos, hB_pos, hδ_le_ρ, h_choice⟩
  let C := B + 1
  have hC_pos : 0 < C := by positivity
  refine ⟨δ, C, hδ_pos, hC_pos, hδ_le_ρ, fun T hT hρ_notin hT_δ => ?_⟩
  rcases h_choice T hT hρ_notin hT_δ with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, h_deriv_bound⟩
  refine ⟨h, h_spec, h_mel_ρ, h_mel_T, ?_⟩
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

# 替换第 2738-2772 行（索引 2737-2771）
lines[2737:2772] = [l + '\n' for l in new_lines]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('done')
