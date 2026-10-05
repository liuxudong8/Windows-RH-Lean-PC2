import re

# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到要替换的部分
old_axiom = '''axiom mellin_constraint_dual_norm_lower_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (c : ℝ), 0 < c ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥
          c * (Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
            ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖)) := by
  sorry'''

new_axiom = '''axiom mellin_constraint_dual_norm_lower_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (c : ℝ), 0 < c ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M := by
  sorry'''

content = content.replace(old_axiom, new_axiom)

# 现在修改定理的签名
old_theorem_sig = '''theorem mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (c : ℝ) (hc_pos : 0 < c) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥
          c * (Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
            ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖)) →'''

new_theorem_sig = '''theorem mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (c : ℝ) (hc_pos : 0 < c) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M →'''

content = content.replace(old_theorem_sig, new_theorem_sig)

# 现在修改证明部分
old_obtain = '''  obtain ⟨hT_spec, hT_mel_T, hT_C2, hT_mel_ρ_ne, hT_bound⟩ := hT_exists'''

new_obtain = '''  obtain ⟨hT_spec, hT_mel_T, hT_C2, hT_mel_ρ_ne, hT_bound, hM_bound⟩ := hT_exists'''

content = content.replace(old_obtain, new_obtain)

# 现在修改证明中的 Finset.sup 部分
old_proof_part = '''    have h5 : ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤
        Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
          ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) := by
      exact Finset.le_sup (Finset.mem_univ (⟨x, by trivial⟩ : {x : ℝ // True}))
    have h6 : ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤
        (1 / c) * max ‖wρ‖ 1 := by
      have h7 : ‖melinTransform hT.toTestFunction ρ‖ ≥
          c * Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
            ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) := hT_bound
      have h8 : 0 < c := hc_pos
      have h9 : 0 < ‖melinTransform hT.toTestFunction ρ‖ := by
        exact norm_pos_iff.mpr hT_mel_ρ_ne
      have h10 : Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
          ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) ≥ 0 := by positivity
      calc
        ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖
          ≤ ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
              ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) := by
            gcongr
            <;> linarith
        _ = ‖wρ‖ * (Finset.sup Finset.univ (fun x : {x : ℝ // True} =>
              ‖(deriv (deriv hT.toTestFunction.toFun) x.val)‖) / ‖melinTransform hT.toTestFunction ρ‖) := by ring
        _ ≤ ‖wρ‖ * (1 / c) := by
            gcongr
            <;> gcongr
            <;> linarith
        _ = (1 / c) * ‖wρ‖ := by ring
        _ ≤ (1 / c) * max ‖wρ‖ 1 := by
            have h11 : ‖wρ‖ ≤ max ‖wρ‖ 1 := le_max_left _ _
            have h12 : 0 ≤ (1 / c) := by positivity
            nlinarith
    exact h6'''

new_proof_part = '''    have h5 : ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M := hM_bound x
    have h6 : ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤
        (1 / c) * max ‖wρ‖ 1 := by
      have h7 : ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M := hT_bound
      have h8 : 0 < c := hc_pos
      have h9 : 0 < ‖melinTransform hT.toTestFunction ρ‖ := by
        exact norm_pos_iff.mpr hT_mel_ρ_ne
      have h10 : 0 ≤ M := by
        have h11 : 0 ≤ ‖(deriv (deriv hT.toTestFunction.toFun) 0)‖ := by positivity
        have h12 : ‖(deriv (deriv hT.toTestFunction.toFun) 0)‖ ≤ M := hM_bound 0
        linarith
      calc
        ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖
          ≤ ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ * M := by
            gcongr
            <;> linarith
        _ = ‖wρ‖ * (M / ‖melinTransform hT.toTestFunction ρ‖) := by ring
        _ ≤ ‖wρ‖ * (1 / c) := by
            gcongr
            <;> gcongr
            <;> linarith
        _ = (1 / c) * ‖wρ‖ := by ring
        _ ≤ (1 / c) * max ‖wρ‖ 1 := by
            have h11 : ‖wρ‖ ≤ max ‖wρ‖ 1 := le_max_left _ _
            have h12 : 0 ≤ (1 / c) := by positivity
            nlinarith
    exact h6'''

content = content.replace(old_proof_part, new_proof_part)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
