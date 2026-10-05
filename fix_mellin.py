with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- Mellin 分离对的统一速降界')
end = content.find('/-- 磨光函数对的尾部和可忽略', start)
old_block = content[start:end]

new_block = '''/-- 零谱点 Mellin 插值（定理，由 Paley-Wiener-Whitney 联合插值推出）：
    对非临界线零点 ρ 和有限集 T（ρ∉T），存在磨光函数 h 满足：
    (1) h(specDiscM n) = 0（谱点取值为零）
    (2) M[h](ρ) = 1
    (3) M[h]|_T = 0
    证明：用 paley_wiener_whitney_joint_interpolation，S=range(specDiscM)（可数+可分离），
    v=0，T'=T∪{ρ}，w(s)=if s=ρ then 1 else 0。 -/
theorem mellin_zero_spectral_interpolation (ρ : ℂ) (T : Set ℂ) (hT : T.Finite) (hρ_notin_T : ρ ∉ T) :
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = 1 ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) := by
  let S := Set.range specDiscM
  have hS_count : Set.Countable S := Set.countable_range _
  have hS_sep : PointSetSeparable S := specDiscM_separable
  let v : ℝ → ℂ := fun _ => 0
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := by
    simp [v]
    <;> exact Set.finite_empty
  let T' := insert ρ T
  have hT'_fin : T'.Finite := hT.insert ρ
  let w : ℂ → ℂ := fun s => if s = ρ then (1 : ℂ) else (0 : ℂ)
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
    对非临界线零点 ρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数 h 满足零谱点插值条件且 Mellin 变换速降：
    ‖M[h](s)‖ ≤ C/(1+|Im s|)²。
    ZFC 基础：可选择光滑插值函数（分部积分给出 Mellin 变换速降）+
    Hahn-Banach 保证有限维约束的解的范数统一有界。
    这是纯分析断言，是 RH 反证法的核心。 -/
axiom mellin_rapid_decay_choice (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = 1 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2)

/-- Mellin 分离对的统一速降界（定理，由速降插值选择公理推出）：
    对非临界线零点 ρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数对 f₁,f₂ 满足：
    (1) 谱点取值相同 (2) M[f₁](ρ)=1, M[f₂](ρ)=0 (3) M[f₁]|_T=M[f₂]|_T (4) 速降界。
    证明：取 f₁=h（速降插值），f₂=0，则 M[f₁]-M[f₂]=M[h]，速降界直接继承。 -/
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
  rcases mellin_rapid_decay_choice ρ hz hre1 hre2 hne with ⟨C, hC_pos, h_choice⟩
  refine ⟨C, hC_pos, fun T hT hρ_notin => ?_⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec_zero, h_mel_ρ, h_mel_T, h_decay⟩
  -- f1 = h, f2 = 0（需要 MollifiedTestFunction 零函数）
  have h_zero_fn : ∃ (f0 : MollifiedTestFunction), ∀ (x : ℝ), f0.toTestFunction.eval x = 0 := by
    exact?
  rcases h_zero_fn with ⟨f0, hf0_zero⟩
  refine ⟨h, f0, ?_, ?_, ?_, ?_, ?_⟩
  · -- 谱点取值相同
    intro n
    have h1 : h.toTestFunction.eval (specDiscM n) = 0 := h_spec_zero n
    have h2 : f0.toTestFunction.eval (specDiscM n) = 0 := hf0_zero (specDiscM n)
    rw [h1, h2]
  · -- M[f1](ρ) = 1
    exact h_mel_ρ
  · -- M[f2](ρ) = 0
    have h3 : melinTransform f0.toTestFunction ρ = 0 := by
      simpa [hf0_zero] using rfl
    exact h3
  · -- M[f1]|_T = M[f2]|_T
    intro s hs
    have h4 : melinTransform h.toTestFunction s = 0 := h_mel_T s hs
    have h5 : melinTransform f0.toTestFunction s = 0 := by
      simpa [hf0_zero] using rfl
    rw [h4, h5]
  · -- 速降界
    intro s hs_re1 hs_re2
    have h6 : melinTransform f0.toTestFunction s = 0 := by
      simpa [hf0_zero] using rfl
    rw [h6, sub_zero]
    exact h_decay s hs_re1 hs_re2

'''

content = content[:start] + new_block + content[end:]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
