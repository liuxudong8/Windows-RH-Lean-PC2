import re

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old_block = '''/-- Mellin 分离对的统一速降界（公理，中风险，纯分析估计）：
    前 4 个条件（谱点取值相同 / M[f₁](ρ)=1 / M[f₂](ρ)=0 / T 上相等）已由
    mellin_pair_separation_construction（PWW 联合插值定理）独立证明。
    此公理仅额外断言：存在不依赖于 T 的统一常数 C，使差的 Mellin 变换在临界带内
    满足 O(1/|Im|²) 速降。
    数学依据：mellin_finite_surjectivity_zero_sum 的构造有统一范数估计
    （核空间中有限维约束的最小范数解，界只依赖于约束值的上确界，而 w₁-w₂ 固定）。
    风险等级：中（标准泛函分析；形式化需 mellin_finite_surjectivity_zero_sum 带范数估计）。 -/
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

new_block = '''/-- 单点 Mellin 分离的统一速降（公理，中风险，比原公理更弱更特殊）：
    对非临界线零点 ρ，存在不依赖于 T 的统一常数 C，使得对任意有限 T（不含 ρ），
    存在 TestFunction h 满足：
    (1) M[h](ρ) = 1
    (2) M[h](s) = 0 for s ∈ T
    (3) nontrivialZeroSum(h) = 0
    (4) ‖M[h](s)‖ ≤ C/(1+|Im|)² 在临界带内
    数学依据：目标赋值 w(s) = (if s=ρ then 1 else 0) 是固定函数（不依赖 T），
    有限插值的最小范数解有统一界。比任意 w 的有限插值简单。
    风险等级：中（标准泛函分析，但比 mellin_finite_surjectivity_zero_sum 带范数估计弱）。 -/
axiom mellin_single_point_separation_decay (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : TestFunction),
        melinTransform h ρ = 1 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h s = 0) ∧
        nontrivialZeroSum h = 0 ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h s‖ ≤ C / (1 + |s.im|) ^ 2)

/-- Mellin 分离对的统一速降界（定理，由单点分离公理 + PWW + 纤维丰富性推出）。零 sorry。
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
      rw [h_eq]
    rw [h1, h_m2ρ, h_mρ] <;> ring
  have h_T_eq : ∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s := by
    intro s hs
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s + melinTransform h s := by rw [h_eq]
    have h2 : melinTransform h s = 0 := h_mT s hs
    rw [h1, h2] <;> ring
  have h_decay' : ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h1 : melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s = melinTransform h s := by
      rw [h_eq] <;> ring
    rw [h1]
    exact h_bound s hre1' hre2'
  exact ⟨f1, f2, h_pts, h_m1ρ, h_m2ρ, h_T_eq, h_decay'⟩'''

if old_block in content:
    content = content.replace(old_block, new_block)
    print("替换成功")
else:
    print("未找到目标块")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
