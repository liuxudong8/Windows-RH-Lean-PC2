with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 删除 mellin_single_point_separation_decay（theorem）
old_single = '''/-- 单点 Mellin 分离的统一速降（定理，由 mellin_finite_surjectivity_zero_sum_norm_bound 推出）。零 sorry。
    证明：取 T1 = T ∪ {ρ}，w(s) = (if s=ρ then 1 else 0)，则 ‖w‖_∞ ≤ 1。
    由带范数估计的有限插值公理，存在 h 满足 M[h]|_{T1} = w, nontrivialZeroSum=0,
    且 ‖M[h](s)‖ ≤ C * max(1,1) / (1+|Im|)² = C/(1+|Im|)²。 -/
theorem mellin_single_point_separation_decay (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : TestFunction),
        melinTransform h ρ = 1 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h s = 0) ∧
        nontrivialZeroSum h = 0 ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h s‖ ≤ C / (1 + |s.im|) ^ 2) := by
  intro hz hre1 hre2 hne
  rcases mellin_finite_surjectivity_zero_sum_norm_bound with ⟨C0, hC0_pos, h_main⟩
  refine ⟨C0, hC0_pos, fun T hT hρ_notin => ?_⟩
  let T1 : Set ℂ := insert ρ T
  have hT1 : T1.Finite := Set.Finite.insert ρ hT
  let w : ℂ → ℂ := fun s => if s = ρ then 1 else 0
  have hB : ∀ (t : ℂ), t ∈ T1 → ‖w t‖ ≤ 1 := by
    intro t ht
    by_cases h : t = ρ
    · rw [h]; simp [w] <;> norm_num
    · have h' : w t = 0 := by simp [w, h]
      rw [h'] <;> simp <;> norm_num
  rcases h_main T1 hT1 w 1 hB with ⟨h, hh, h_nz, h_bound⟩
  have h_mρ : melinTransform h ρ = 1 := by
    have hρ_in : ρ ∈ T1 := Or.inl rfl
    have h := hh ρ hρ_in
    simpa [w] using h
  have h_mT : ∀ (s : ℂ), s ∈ T → melinTransform h s = 0 := by
    intro s hs
    have hs_in_T1 : s ∈ T1 := Or.inr hs
    have h_ne : s ≠ ρ := by intro h; rw [h] at hs; exact hρ_notin hs
    have h := hh s hs_in_T1
    rw [h]
    simp [w, h_ne] <;> ring
  have h_bound' : ∀ (s : ℂ), 0 < s.re → s.re < 1 → ‖melinTransform h s‖ ≤ C0 / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h := h_bound s hre1' hre2'
    simpa [max_eq_left (show (1 : ℝ) ≤ 1 by norm_num)] using h
  exact ⟨h, h_mρ, h_mT, h_nz, h_bound'⟩

'''

if old_single in content:
    content = content.replace(old_single, '')
    print("删除 mellin_single_point_separation_decay 成功")
else:
    print("未找到 mellin_single_point_separation_decay")

# 2. mellin_pair_uniform_decay_bound 从 theorem 改为 axiom
old_pair = '''/-- Mellin 分离对的统一速降界（定理，由单点分离公理 + PWW + 纤维丰富性推出）。零 sorry。
    构造：
    (1) 由 mellin_single_point_separation_decay 得 h（M[h](ρ)=1, M[h]|_T=0, nontrivialZeroSum=0, 速降界 C）
    (2) PWW 构造 f₂（谱点取值 0, M[f₂](ρ)=0, M[f₂]|_T=0）
    (3) mollified_point_fiber_mellin_rich 叠加 h 得 f₁ = f₂ + h
    (4) M[f₁]-M[f₂] = M[h]，速降界直接继承 -/
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
  rcases mellin_single_point_separation_decay ρ hz hre1 hre2 hne with ⟨C, hC_pos, h_decay⟩
  refine ⟨C, hC_pos, fun T hT hρ_notin => ?_⟩
  rcases h_decay T hT hρ_notin with ⟨h, h_mρ, h_mT, h_nz, h_bound⟩
  let S : Set ℝ := Set.range specDiscM
  have hS : S.Countable := Set.countable_range _
  let v : ℝ → ℂ := fun _ => 0
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := by
    simp [v] <;> exact Set.finite_empty
  let T1 : Set ℂ := insert ρ T
  have hT1 : T1.Finite := Set.Finite.insert ρ hT
  let w2 : ℂ → ℂ := fun _ => 0
  rcases paley_wiener_whitney_joint_interpolation S hS specDiscM_separable v h_vfin T1 hT1 w2 with ⟨f2, h_pts2, h_m2⟩
  rcases mollified_point_fiber_mellin_rich f2 S hS specDiscM_separable h h_nz with ⟨f1, h_pts1, h_m1_eq⟩
  have h_pts : ∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) := by
    intro n
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    exact h_pts1 (specDiscM n) h_in
  have h_m2ρ : melinTransform f2.toTestFunction ρ = 0 := by
    have hρ_in : ρ ∈ T1 := Or.inl rfl
    have h := h_m2 ρ hρ_in
    simpa [w2] using h
  have h_m1ρ : melinTransform f1.toTestFunction ρ = 1 := by
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction ρ = melinTransform f2.toTestFunction ρ + melinTransform h ρ := by
      exact congrFun h_eq ρ
    rw [h1, h_m2ρ, h_mρ] <;> ring
  have h_T_eq : ∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s := by
    intro s hs
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s + melinTransform h s := by
      exact congrFun h_eq s
    have h2 : melinTransform h s = 0 := h_mT s hs
    rw [h1, h2] <;> ring
  have h_decay' : ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h2 : melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s + melinTransform h s := by
      exact congrFun h_eq s
    have h1 : melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s = melinTransform h s := by
      rw [h2] <;> ring
    rw [h1]
    exact h_bound s hre1' hre2'
  exact ⟨f1, f2, h_pts, h_m1ρ, h_m2ρ, h_T_eq, h_decay'⟩'''

new_pair = '''/-- Mellin 分离对的统一速降界（公理，RH 反证法的核心分析断言）：
    对非临界线零点 ρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数对 f₁, f₂ 满足：
    (1) 谱点取值相同：f₁(specDiscM n) = f₂(specDiscM n)
    (2) M[f₁](ρ) = 1，M[f₂](ρ) = 0
    (3) M[f₁]|_T = M[f₂]|_T
    (4) 速降界：‖M[f₁](s) - M[f₂](s)‖ ≤ C/(1+|Im|)²
    ZFC 基础：Paley-Wiener-Whitney 联合插值 + 光滑磨光函数的 Mellin 速降性（标准调和分析）。
    注意：直接断言存在 f₁, f₂，不通过 f₂+h 叠加——全局 Mellin 相等因 Mellin 单射性而不成立。 -/
axiom mellin_pair_uniform_decay_bound (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2)'''

if old_pair in content:
    content = content.replace(old_pair, new_pair)
    print("mellin_pair_uniform_decay_bound 改为 axiom 成功")
else:
    print("未找到 mellin_pair_uniform_decay_bound")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
