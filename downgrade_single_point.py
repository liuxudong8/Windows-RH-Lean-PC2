with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old_block = '''/-- 单点 Mellin 分离的统一速降（公理，中风险，纯分析估计）：
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

new_block = '''/-- 单点 Mellin 分离的统一速降（定理，由 mellin_finite_surjectivity_zero_sum_norm_bound 推出）。零 sorry。
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
    have h_max : max (1 : ℝ) 1 = 1 := by simp
    rw [h_max] at h
    exact h
  exact ⟨h, h_mρ, h_mT, h_nz, h_bound'⟩'''

if old_block in content:
    content = content.replace(old_block, new_block)
    print("stage_4.lean 替换成功")
else:
    print("未找到目标块")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
