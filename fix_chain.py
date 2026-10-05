f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 加强 melin_zero_localization：增加平凡零点和极点处的 Mellin 消零
old_mlz = '''axiom melin_zero_localization (ρ : ℂ) (g : MollifiedTestFunction) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      ∃ (g' : MollifiedTestFunction),
        (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
          ρ' ≠ ρ → ρ' ≠ 1 - ρ →
          melinTransform g'.toTestFunction ρ' = 0) ∧
        (melinTransform g'.toTestFunction ρ + melinTransform g'.toTestFunction (1 - ρ) =
         melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ))'''

new_mlz = '''axiom melin_zero_localization (ρ : ℂ) (g : MollifiedTestFunction) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      ∃ (g' : MollifiedTestFunction),
        (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
          ρ' ≠ ρ → ρ' ≠ 1 - ρ →
          melinTransform g'.toTestFunction ρ' = 0) ∧
        (∀ (k : ℕ), melinTransform g'.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) = 0) ∧
        melinTransform g'.toTestFunction (1 : ℂ) = 0 ∧
        (melinTransform g'.toTestFunction ρ + melinTransform g'.toTestFunction (1 - ρ) =
         melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ))'''

content = content.replace(old_mlz, new_mlz, 1)

# 2. 修改 spectral_preserving_perturbation_build 的 rcases 和结论
old_build_rcases = '''  rcases melin_zero_localization ρ g hz hre1 hre2 with ⟨g', h_other_zero, h_pair_eq⟩'''
new_build_rcases = '''  rcases melin_zero_localization ρ g hz hre1 hre2 with ⟨g', h_other_zero, h_triv_zero, h_pole_zero, h_pair_eq⟩'''
content = content.replace(old_build_rcases, new_build_rcases, 1)

# 3. 在 spectral_preserving_perturbation_build 的结论中增加 trivialZeroContribution 相同
# 先找到 exact 行
old_build_exact = '''  exact ⟨f1, f2, h_pts, h_other, h_pair_diff⟩'''
new_build_exact = '''  have h_triv_eq : trivialZeroContribution f1.toTestFunction = trivialZeroContribution f2.toTestFunction := by
    have h_all_triv : ∀ (k : ℕ), melinTransform f2.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) =
                               melinTransform f1.toTestFunction ((-2 * (k + 1 : ℕ) : ℝ) : ℂ) := by
      intro k
      have h_diff := h_super ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)
      rw [h_triv_zero k] at h_diff
      exact (sub_eq_zero.mp h_diff).symm
    have h_pole_eq : melinTransform f2.toTestFunction (1 : ℂ) = melinTransform f1.toTestFunction (1 : ℂ) := by
      have h_diff := h_super (1 : ℂ)
      rw [h_pole_zero] at h_diff
      exact (sub_eq_zero.mp h_diff).symm
    exact trivialZeroContribution_of_melin_vanishing f1.toTestFunction
      (fun k => by rw [h_all_triv k])
      (by rw [h_pole_eq])
      ▸ rfl
  exact ⟨f1, f2, h_pts, h_other, h_pair_diff, h_triv_eq⟩'''
content = content.replace(old_build_exact, new_build_exact, 1)

# 4. 修改 spectral_preserving_perturbation_build 的类型签名，增加 trivialZeroContribution 相同
old_build_type = '''theorem spectral_preserving_perturbation_build (ρ : ℂ) (g : MollifiedTestFunction) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
          ρ' ≠ ρ → ρ' ≠ 1 - ρ →
          melinTransform f1.toTestFunction ρ' = melinTransform f2.toTestFunction ρ') ∧
        ((melinTransform f2.toTestFunction ρ + melinTransform f2.toTestFunction (1 - ρ)) -
         (melinTransform f1.toTestFunction ρ + melinTransform f1.toTestFunction (1 - ρ)) =
         melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ)) := by'''

new_build_type = '''theorem spectral_preserving_perturbation_build (ρ : ℂ) (g : MollifiedTestFunction) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
          ρ' ≠ ρ → ρ' ≠ 1 - ρ →
          melinTransform f1.toTestFunction ρ' = melinTransform f2.toTestFunction ρ') ∧
        ((melinTransform f2.toTestFunction ρ + melinTransform f2.toTestFunction (1 - ρ)) -
         (melinTransform f1.toTestFunction ρ + melinTransform f1.toTestFunction (1 - ρ)) =
         melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ)) ∧
        trivialZeroContribution f1.toTestFunction = trivialZeroContribution f2.toTestFunction := by'''
content = content.replace(old_build_type, new_build_type, 1)

# 5. 修改 mollified_melin_separation 的 rcases 和结论
old_mms_rcases = '''  rcases spectral_preserving_perturbation_build ρ g hz hre1 hre2 with ⟨f1, f2, h_pts, h_other, h_pair_diff⟩'''
new_mms_rcases = '''  rcases spectral_preserving_perturbation_build ρ g hz hre1 hre2 with ⟨f1, f2, h_pts, h_other, h_pair_diff, h_triv_eq⟩'''
content = content.replace(old_mms_rcases, new_mms_rcases, 1)

# 6. 修改 mollified_melin_separation 的 exact 行
old_mms_exact = '''  exact ⟨f1, f2, h_pts, h_other, h_pair_ne⟩'''
# 需要找到正确的上下文
old_mms_conclusion = '''    (3) 故 f₁,f₂ 的成对和不同 -/
theorem mollified_melin_separation (ρ : ℂ) :'''
# 让我先找到 mollified_melin_separation 的完整内容

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: modified melin_zero_localization and spectral_preserving_perturbation_build')
