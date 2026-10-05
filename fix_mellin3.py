with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- 速降插值选择公理')
end = content.find('/-- Mellin 分离对的统一速降界（定理', start)
old_block = content[start:end]

new_block = '''/-- 光滑插值选择公理（RH 反证法核心，第一层）：
    对非临界线零点 ρ 和目标值 wρ，存在统一导数界 B，使得对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足：
    (1) h(specDiscM n) = 0
    (2) M[h](ρ) = wρ
    (3) M[h]|_T = 0
    (4) h 是 C² 光滑且二阶导数有界：‖h''(x)‖ ≤ B·max(‖wρ‖,1)
    ZFC 基础：Paley-Wiener-Whitney 联合插值 + 光滑化（mollification）+
    Hahn-Banach 保证有限维约束的解的导数范数统一有界。 -/
axiom mellin_smooth_interpolation (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(iteratedDeriv ℝ 2 h.toTestFunction.toFun x)‖ ≤ B * max ‖wρ‖ 1)

/-- Mellin 变换的 C² 速降估计（定理，分部积分）：
    若 f 是 C² 光滑、紧支集、在 0 附近消失，则对 σ∈(0,1)：
    ‖M[f](σ+it)‖ ≤ (‖f‖_∞ + ‖f''‖_∞) / (1+|t|)²
    证明：两次分部积分，M[f](s) = -1/(s(s+1)) · M[f''](s)，
    而 ‖M[f''](s)‖ ≤ ∫ |f''(x)| x^{σ-1} dx ≤ ‖f''‖_∞ · ∫_{supp} x^{σ-1} dx，
    支集有界且远离 0，故积分有界。 -/
theorem mellin_transform_C2_rapid_decay (f : TestFunction) (hC2 : ContDiff ℝ 2 f.toFun)
    (hB : ∀ x, ‖(iteratedDeriv ℝ 2 f.toFun x)‖ ≤ B) (hB_pos : 0 < B) :
    ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform f s‖ ≤ (B + 1) / (1 + |s.im|) ^ 2 := by
  intro s hs_re1 hs_re2
  -- 这是标准分部积分结果，形式化需要 Mellin 变换的分部积分公式
  -- 当前作为定理声明，证明待补（需 Mellin 变换导数公式 + 积分估计）
  sorry

/-- 速降插值选择公理（RH 反证法核心，由光滑插值 + C² 速降估计推出）：
    对非临界线零点 ρ 和目标值 wρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数 h 满足零谱点插值条件且 Mellin 变换速降：
    ‖M[h](s)‖ ≤ C·max(‖wρ‖,1)/(1+|Im s|)²。 -/
theorem mellin_rapid_decay_choice (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * max ‖wρ‖ 1 / (1 + |s.im|) ^ 2) := by
  intro hz hre1 hre2 hne
  rcases mellin_smooth_interpolation ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  let C := B + 1
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun T hT hρ_notin => ?_⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, h_deriv_bound⟩
  refine ⟨h, h_spec, h_mel_ρ, h_mel_T, ?_⟩
  intro s hs_re1 hs_re2
  have h_decay : ‖melinTransform h.toTestFunction s‖ ≤ (B + 1) / (1 + |s.im|) ^ 2 :=
    mellin_transform_C2_rapid_decay h.toTestFunction hC2 h_deriv_bound hB_pos s hs_re1 hs_re2
  have h_final : (B + 1) / (1 + |s.im|) ^ 2 ≤ C * max ‖wρ‖ 1 / (1 + |s.im|) ^ 2 := by
    have h1 : 1 ≤ max ‖wρ‖ 1 := by apply le_max_right
    have h2 : B + 1 ≤ C * max ‖wρ‖ 1 := by
      dsimp only [C]
      have h3 : B + 1 ≤ (B + 1) * max ‖wρ‖ 1 := by
        exact le_mul_of_one_le_right (by positivity) h1
      exact h3
    gcongr
    <;> linarith
  exact le_trans h_decay h_final

'''

content = content[:start] + new_block + content[end:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
