f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 修复 h_pair 证明
old1 = """    have h_pair : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) ≠ 0 := by
    by_cases h_eq : ρ = 1 - ρ
    · have h1 : 1 - ρ = ρ := by exact h_eq.symm
      rw [h1, h_rho, h_rho] <;> norm_num
    · have h_1mrho : melinTransform g0.toTestFunction (1 - ρ) = 0 := by
        rw [hg0 (1 - ρ) h_1mrho_in]
        have h_ne : (1 - ρ) ≠ ρ := by intro h; exact h_eq h.symm
        simp [v, h_ne]
      rw [h_rho, h_1mrho] <;> norm_num"""

new1 = """    have h_pair : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) ≠ 0 := by
    by_cases h_eq : ρ = 1 - ρ
    · have h1 : 1 - ρ = ρ := by exact h_eq.symm
      have h_sum : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) = 2 := by
        rw [h1, h_rho] <;> norm_num
      rw [h_sum] <;> norm_num
    · have h_1mrho : melinTransform g0.toTestFunction (1 - ρ) = 0 := by
        rw [hg0 (1 - ρ) h_1mrho_in]
        have h_ne : (1 - ρ) ≠ ρ := by intro h; exact h_eq h.symm
        simp [v, h_ne]
      have h_sum : melinTransform g0.toTestFunction ρ + melinTransform g0.toTestFunction (1 - ρ) = 1 := by
        rw [h_rho, h_1mrho] <;> norm_num
      rw [h_sum] <;> norm_num"""

content = content.replace(old1, new1, 1)

# 修复消零条件：用 simpa [v]
old2 = """    exact hg0 ρ' h_in"""
new2 = """    simpa [v] using hg0 ρ' h_in"""
content = content.replace(old2, new2, 1)

old3 = """      exact hg0 _ h_in"""
new3 = """      simpa [v] using hg0 _ h_in"""
content = content.replace(old3, new3, 1)

old4 = """        exact hg0 (1 : ℂ) h_in"""
new4 = """        simpa [v] using hg0 (1 : ℂ) h_in"""
content = content.replace(old4, new4, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: fixed rw and simpa')
