with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 修改 mellin_rapid_decay_choice
old1_start = content.find('/-- 速降插值选择定理（由光滑插值 + C² 速降估计推出）')
old1_end = content.find('/-- Mellin 分离对的统一速降界', old1_start)
old1 = content[old1_start:old1_end]

new1 = '''/-- 速降插值选择定理（由光滑插值 + C² 速降估计推出）：
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

'''

content = content[:old1_start] + new1 + content[old1_end:]

# 2. 修改 mellin_pair_uniform_decay_bound
old2_start = content.find('/-- Mellin 分离对的统一速降界')
old2_end = content.find('mollified_pair_tail_sum_negligible', old2_start)
# 找到定理结束
old2_end = content.find('\n\n', old2_start + 100)
old2 = content[old2_start:old2_end]

new2 = '''/-- Mellin 分离对的统一速降界（定理，由速降插值选择定理推出）：
    对非临界线零点 ρ，存在 δ > 0 和统一常数 C，使得对任意有限 T（ρ∉T，且 T 中点满足 s.re ≥ δ），
    存在磨光函数对 f₁,f₂ 满足速降界。
    证明：用 mellin_rapid_decay_choice 分别构造 h₁(wρ=1) 和 h₂(wρ=0)。 -/
theorem mellin_pair_uniform_decay_bound (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (δ C : ℝ), 0 < δ ∧ 0 < C ∧ δ ≤ ρ.re ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T → (∀ s ∈ T, δ ≤ s.re) →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2) := by
  intro hz hre1 hre2 hne
  rcases mellin_rapid_decay_choice ρ 1 hz hre1 hre2 hne with ⟨δ1, C1, hδ1_pos, hC1_pos, hδ1_le, h_choice1⟩
  rcases mellin_rapid_decay_choice ρ 0 hz hre1 hre2 hne with ⟨δ2, C2, hδ2_pos, hC2_pos, hδ2_le, h_choice2⟩
  let δ := min δ1 δ2
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_ρ : δ ≤ ρ.re := by
    dsimp only [δ]
    have h1 : δ ≤ δ1 := by apply min_le_left
    linarith
  let C := 2 * max C1 C2
  have hC_pos : 0 < C := by positivity
  refine ⟨δ, C, hδ_pos, hC_pos, hδ_le_ρ, fun T hT hρ_notin hT_δ => ?_⟩
  have hT_δ1 : ∀ s ∈ T, δ1 ≤ s.re := by
    intro s hs
    have h5 : δ ≤ s.re := hT_δ s hs
    have h6 : δ ≤ δ1 := by apply min_le_left
    linarith
  have hT_δ2 : ∀ s ∈ T, δ2 ≤ s.re := by
    intro s hs
    have h5 : δ ≤ s.re := hT_δ s hs
    have h6 : δ ≤ δ2 := by apply min_le_right
    linarith
  rcases h_choice1 T hT hρ_notin hT_δ1 with ⟨f1, h1_spec, h1_mel_ρ, h1_mel_T, h1_decay⟩
  rcases h_choice2 T hT hρ_notin hT_δ2 with ⟨f2, h2_spec, h2_mel_ρ, h2_mel_T, h2_decay⟩
  refine ⟨f1, f2, ?_, h1_mel_ρ, h2_mel_ρ, ?_, ?_⟩
  · -- 谱点取值相同（都为 0）
    intro n
    rw [h1_spec n, h2_spec n]
  · -- Mellin 在 T 上相同（都为 0）
    intro s hs
    rw [h1_mel_T s hs, h2_mel_T s hs]
  · -- 速降界
    intro s hs_re1 hs_re2
    have h1 : ‖melinTransform f1.toTestFunction s‖ ≤ C1 * max (1 : ℝ) 1 / (1 + |s.im|) ^ 2 := h1_decay s hs_re1 hs_re2
    have h2 : ‖melinTransform f2.toTestFunction s‖ ≤ C2 * max (0 : ℝ) 1 / (1 + |s.im|) ^ 2 := h2_decay s hs_re1 hs_re2
    have h3 : ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤
        ‖melinTransform f1.toTestFunction s‖ + ‖melinTransform f2.toTestFunction s‖ := by
      exact norm_sub_le _ _
    have h4 : ‖melinTransform f1.toTestFunction s‖ + ‖melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2 := by
      simp [h1, h2, C] <;> ring_nf <;> norm_num <;> linarith
    exact le_trans h3 h4

'''

content = content[:old2_start] + new2 + content[old2_end:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
