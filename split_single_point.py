with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old_block = '''/-- 单点 Mellin 分离的统一速降（公理，中风险，比原公理更弱更特殊）：
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
          ‖melinTransform h s‖ ≤ C / (1 + |s.im|) ^ 2)'''

new_block = '''/-- 单点 Mellin 分离的存在性（定理，由 mellin_finite_surjectivity_zero_sum 推出）。零 sorry。
    对非临界线零点 ρ 和任意有限 T（不含 ρ），存在 TestFunction h 满足：
    (1) M[h](ρ) = 1
    (2) M[h](s) = 0 for s ∈ T
    (3) nontrivialZeroSum(h) = 0
    证明：取 T1 = T ∪ {ρ}，w(s) = (if s=ρ then 1 else 0)，由 mellin_finite_surjectivity_zero_sum 即得。 -/
theorem mellin_single_point_separation (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : TestFunction),
      melinTransform h ρ = 1 ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h s = 0) ∧
      nontrivialZeroSum h = 0 := by
  intro hz hre1 hre2 hne T hT hρ_notin
  let T1 : Set ℂ := insert ρ T
  have hT1 : T1.Finite := Set.Finite.insert ρ hT
  let w : ℂ → ℂ := fun s => if s = ρ then 1 else 0
  rcases mellin_finite_surjectivity_zero_sum T1 hT1 w with ⟨h, hh, h_nz⟩
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
  exact ⟨h, h_mρ, h_mT, h_nz⟩

/-- 单点 Mellin 分离的统一速降（公理，中风险，纯分析估计）：
    存在性（前 3 个条件）已由 mellin_single_point_separation 定理独立证明。
    此公理仅额外断言：存在不依赖于 T 的统一常数 C，使 h 的 Mellin 变换在临界带内
    满足 O(1/|Im|²) 速降。
    数学依据：目标赋值 w(s) = (if s=ρ then 1 else 0) 是固定函数（不依赖 T），
    有限插值的最小范数解有统一界。
    风险等级：中（标准泛函分析；统一界是真正的分析断言，无法从存在性推出）。 -/
axiom mellin_single_point_separation_decay (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : TestFunction),
        melinTransform h ρ = 1 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h s = 0) ∧
        nontrivialZeroSum h = 0 ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h s‖ ≤ C / (1 + |s.im|) ^ 2)'''

if old_block in content:
    content = content.replace(old_block, new_block)
    print("替换成功")
else:
    print("未找到目标块")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
