# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修正变量名：把 hT_exists 里的 hT 改成 hT'
old_proof = '''  intro hz hre1 hre2 hne T hT hρ_notin hT_exists
  obtain ⟨hT_spec, hT_mel_T, hT_C2, hT_mel_ρ_ne, hT_bound, hM_bound⟩ := hT_exists
  -- 简单构造：直接用 hT 缩放
  let scalar : ℂ := wρ / melinTransform hT.toTestFunction ρ
  refine ⟨scalar • hT, ?_, ?_, ?_, ?_, ?_⟩
  · -- 谱点取值为 0
    simpa [scalar, hT_spec] using smul_zero _
  · -- melinTransform h ρ = wρ
    have h1 : melinTransform (scalar • hT).toTestFunction ρ = scalar * melinTransform hT.toTestFunction ρ := by
      exact?
    rw [h1, scalar, div_mul_cancel₀ _ hT_mel_ρ_ne]
  · -- melinTransform h s = 0 对所有 s ∈ T
    intro s hs
    have h2 : melinTransform (scalar • hT).toTestFunction s = scalar * melinTransform hT.toTestFunction s := by exact?
    rw [h2, hT_mel_T s hs, mul_zero]
  · -- C² 光滑
    exact ContDiff.const_smul hT_C2 _
  · -- 二阶导数范数界
    intro x
    have h3 : ‖(deriv (deriv (scalar • hT).toTestFunction.toFun) x)‖ =
        ‖scalar‖ * ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ := by
      simpa [smul_eq_mul, norm_mul] using rfl
    rw [h3]
    have h4 : ‖scalar‖ = ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ := by
      simp [scalar, norm_div]
      <;> ring
    rw [h4]
    have h5 : ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M := hM_bound x
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

new_proof = '''  intro hz hre1 hre2 hne T hT_finite hρ_notin hT_exists
  obtain ⟨hT', M, hT_spec, hT_mel_T, hT_C2, hT_mel_ρ_ne, hT_bound, hM_bound⟩ := hT_exists
  -- 简单构造：直接用 hT' 缩放
  let scalar : ℂ := wρ / melinTransform hT'.toTestFunction ρ
  refine ⟨scalar • hT', ?_, ?_, ?_, ?_, ?_⟩
  · -- 谱点取值为 0
    simpa [scalar, hT_spec] using smul_zero _
  · -- melinTransform h ρ = wρ
    have h1 : melinTransform (scalar • hT').toTestFunction ρ = scalar * melinTransform hT'.toTestFunction ρ := by
      exact?
    rw [h1, scalar, div_mul_cancel₀ _ hT_mel_ρ_ne]
  · -- melinTransform h s = 0 对所有 s ∈ T
    intro s hs
    have h2 : melinTransform (scalar • hT').toTestFunction s = scalar * melinTransform hT'.toTestFunction s := by exact?
    rw [h2, hT_mel_T s hs, mul_zero]
  · -- C² 光滑
    exact ContDiff.const_smul hT_C2 _
  · -- 二阶导数范数界
    intro x
    have h3 : ‖(deriv (deriv (scalar • hT').toTestFunction.toFun) x)‖ =
        ‖scalar‖ * ‖(deriv (deriv hT'.toTestFunction.toFun) x)‖ := by
      simpa [smul_eq_mul, norm_mul] using rfl
    rw [h3]
    have h4 : ‖scalar‖ = ‖wρ‖ / ‖melinTransform hT'.toTestFunction ρ‖ := by
      simp [scalar, norm_div]
      <;> ring
    rw [h4]
    have h5 : ‖(deriv (deriv hT'.toTestFunction.toFun) x)‖ ≤ M := hM_bound x
    have h6 : ‖wρ‖ / ‖melinTransform hT'.toTestFunction ρ‖ * ‖(deriv (deriv hT'.toTestFunction.toFun) x)‖ ≤
        (1 / c) * max ‖wρ‖ 1 := by
      have h7 : ‖melinTransform hT'.toTestFunction ρ‖ ≥ c * M := hT_bound
      have h8 : 0 < c := hc_pos
      have h9 : 0 < ‖melinTransform hT'.toTestFunction ρ‖ := by
        exact norm_pos_iff.mpr hT_mel_ρ_ne
      have h10 : 0 ≤ M := by
        have h11 : 0 ≤ ‖(deriv (deriv hT'.toTestFunction.toFun) 0)‖ := by positivity
        have h12 : ‖(deriv (deriv hT'.toTestFunction.toFun) 0)‖ ≤ M := hM_bound 0
        linarith
      calc
        ‖wρ‖ / ‖melinTransform hT'.toTestFunction ρ‖ * ‖(deriv (deriv hT'.toTestFunction.toFun) x)‖
          ≤ ‖wρ‖ / ‖melinTransform hT'.toTestFunction ρ‖ * M := by
            gcongr
            <;> linarith
        _ = ‖wρ‖ * (M / ‖melinTransform hT'.toTestFunction ρ‖) := by ring
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

content = content.replace(old_proof, new_proof)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
