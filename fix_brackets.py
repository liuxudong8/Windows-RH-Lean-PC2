# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到定理签名部分
old_sig = '''theorem mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (c : ℝ) (hc_pos : 0 < c) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M →
      ∃ (h : MollifiedTestFunction),'''

new_sig = '''theorem mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (c : ℝ) (hc_pos : 0 < c) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ((∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M) →
      ∃ (h : MollifiedTestFunction),'''

content = content.replace(old_sig, new_sig)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
