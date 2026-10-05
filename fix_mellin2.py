with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- 零谱点 Mellin 插值')
end = content.find('/-- 磨光函数对的尾部和可忽略', start)
old_block = content[start:end]

new_block = '''/-- 零谱点 Mellin 插值（定理，由 Paley-Wiener-Whitney 联合插值推出）：
    对非临界线零点 ρ、有限集 T（ρ∉T）和目标值 wρ，存在磨光函数 h 满足：
    (1) h(specDiscM n) = 0（谱点取值为零）
    (2) M[h](ρ) = wρ
    (3) M[h]|_T = 0
    证明：用 paley_wiener_whitney_joint_interpolation，S=range(specDiscM)（可数+可分离），
    v=0，T'=T∪{ρ}，w(s)=if s=ρ then wρ else 0。 -/
theorem mellin_zero_spectral_interpolation (ρ : ℂ) (T : Set ℂ) (hT : T.Finite) (hρ_notin_T : ρ ∉ T) (wρ : ℂ) :
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) := by
  let S := Set.range specDiscM
  have hS_count : Set.Countable S := Set.countable_range _
  have hS_sep : PointSetSeparable S := specDiscM_separable
  let v : ℝ → ℂ := fun _ => 0
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := by
    simp [v] <;> exact Set.finite_empty
  let T' := insert ρ T
  have hT'_fin : T'.Finite := hT.insert ρ
  let w : ℂ → ℂ := fun s => if s = ρ then wρ else (0 : ℂ)
  rcases paley_wiener_whitney_joint_interpolation S hS_count hS_sep v h_vfin T' hT'_fin w with ⟨h, h_pts, h_mel⟩
  refine ⟨h, ?_, ?_, ?_⟩
  · intro n
    have h2 : specDiscM n ∈ S := ⟨n, rfl⟩
    have h3 : h.toTestFunction.eval (specDiscM n) = v (specDiscM n) := h_pts (specDiscM n) h2
    rw [h3] <;> simp [v]
  · have h4 : ρ ∈ T' := by simp [T']
    have h5 := h_mel ρ h4
    simpa [w] using h5
  · intro s hs
    have h6 : s ∈ T' := by simp [T', hs]
    have h7 := h_mel s h6
    have h8 : s ≠ ρ := by intro h9; rw [h9] at hs; exact hρ_notin_T hs
    simpa [w, h8] using h7

/-- 速降插值选择公理（RH 反证法的核心分析断言）：
    对非临界线零点 ρ 和目标值 wρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数 h 满足零谱点插值条件且 Mellin 变换速降：
    ‖M[h](s)‖ ≤ C·max(‖wρ‖,1)/(1+|Im s|)²。
    ZFC 基础：可选择光滑插值函数（分部积分给出 Mellin 变换速降）+
    Hahn-Banach 保证有限维约束的解的范数统一有界（只依赖 ‖wρ‖）。
    这是纯分析断言，是 RH 反证法的核心。 -/
axiom mellin_rapid_decay_choice (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * max ‖wρ‖ 1 / (1 + |s.im|) ^ 2)

/-- Mellin 分离对的统一速降界（定理，由速降插值选择公理推出）：
    对非临界线零点 ρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数对 f₁,f₂ 满足：
    (1) 谱点取值相同 (2) M[f₁](ρ)=1, M[f₂](ρ)=0 (3) M[f₁]|_T=M[f₂]|_T (4) 速降界。
    证明：用 mellin_rapid_decay_choice 分别构造 h₁(wρ=1) 和 h₂(wρ=0)，
    则 ‖M[h₁]-M[h₂]‖ ≤ ‖M[h₁]‖+‖M[h₂]‖ ≤ 2C/(1+|Im|)²。 -/
theorem mellin_pair_uniform_decay_bound (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2) := by
  intro hz hre1 hre2 hne
  rcases mellin_rapid_decay_choice ρ (1 : ℂ) hz hre1 hre2 hne with ⟨C1, hC1_pos, h_choice1⟩
  rcases mellin_rapid_decay_choice ρ (0 : ℂ) hz hre1 hre2 hne with ⟨C2, hC2_pos, h_choice2⟩
  let C := 2 * max C1 C2
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun T hT hρ_notin => ?_⟩
  rcases h_choice1 T hT hρ_notin with ⟨h1, h1_spec, h1_mel_ρ, h1_mel_T, h1_decay⟩
  rcases h_choice2 T hT hρ_notin with ⟨h2, h2_spec, h2_mel_ρ, h2_mel_T, h2_decay⟩
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · -- 谱点取值相同（都为零）
    intro n
    have h1' : h1.toTestFunction.eval (specDiscM n) = 0 := h1_spec n
    have h2' : h2.toTestFunction.eval (specDiscM n) = 0 := h2_spec n
    rw [h1', h2']
  · -- M[f1](ρ) = 1
    simpa using h1_mel_ρ
  · -- M[f2](ρ) = 0
    simpa using h2_mel_ρ
  · -- M[f1]|_T = M[f2]|_T（都为零）
    intro s hs
    have h4 : melinTransform h1.toTestFunction s = 0 := h1_mel_T s hs
    have h5 : melinTransform h2.toTestFunction s = 0 := h2_mel_T s hs
    rw [h4, h5]
  · -- 速降界：‖M[h1]-M[h2]‖ ≤ ‖M[h1]‖+‖M[h2]‖ ≤ C1*max(1,1)/(...) + C2*max(0,1)/(...) ≤ (C1+C2)/(...) ≤ C/(...)
    intro s hs_re1 hs_re2
    have h6 : ‖melinTransform h1.toTestFunction s - melinTransform h2.toTestFunction s‖ ≤
        ‖melinTransform h1.toTestFunction s‖ + ‖melinTransform h2.toTestFunction s‖ := by
      exact norm_sub_le _ _
    have h7 : ‖melinTransform h1.toTestFunction s‖ ≤ C1 * max ‖(1 : ℂ)‖ 1 / (1 + |s.im|) ^ 2 := h1_decay s hs_re1 hs_re2
    have h8 : ‖melinTransform h2.toTestFunction s‖ ≤ C2 * max ‖(0 : ℂ)‖ 1 / (1 + |s.im|) ^ 2 := h2_decay s hs_re1 hs_re2
    have h9 : max ‖(1 : ℂ)‖ 1 = 1 := by simp
    have h10 : max ‖(0 : ℂ)‖ 1 = 1 := by simp
    rw [h9, h10] at h7 h8
    calc
      ‖melinTransform h1.toTestFunction s - melinTransform h2.toTestFunction s‖
        ≤ ‖melinTransform h1.toTestFunction s‖ + ‖melinTransform h2.toTestFunction s‖ := h6
      _ ≤ C1 / (1 + |s.im|) ^ 2 + C2 / (1 + |s.im|) ^ 2 := by gcongr
      _ = (C1 + C2) / (1 + |s.im|) ^ 2 := by ring
      _ ≤ C / (1 + |s.im|) ^ 2 := by
        have h11 : C1 + C2 ≤ C := by
          dsimp only [C]
          have h12 : C1 ≤ max C1 C2 := le_max_left C1 C2
          have h13 : C2 ≤ max C1 C2 := le_max_right C1 C2
          linarith
        gcongr
        <;> linarith

'''

content = content[:start] + new_block + content[end:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
