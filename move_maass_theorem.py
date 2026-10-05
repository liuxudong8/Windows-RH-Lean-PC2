with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. 把新添加的 theorem（在原位置）恢复为 axiom
theorem_block = '''/-- 正向谱-零点对应（定理，由分布支撑比较推出）：
    每个 Maass 谱参数 t_n 对应 ζ 非平凡零点 ρ_n = 1/2 + i·t_n。

    证明（与 zero_im_matches_maass_param 对称）：
    (1) spectral_zero_equality: spectralSum(f) = nontrivialZeroSum(f)
    (2) distribution_equality_support: supp(spectralSum) = supp(nontrivialZeroSum)
    (3) spectral_side_support: supp(spectralSum) = {1/4+t_n²}
    (4) nontrivialZeroSum_support: supp(nontrivialZeroSum) = {1/4+(Im ρ)² : 临界线上零点}
    (5) 所以 {1/4+t_n²} = {1/4+(Im ρ)²}
    (6) 对任意 n，1/4+t_n² ∈ 左边 = 右边
    (7) 故 ∃临界线上零点 ρ, 1/4+(Im ρ)² = 1/4+t_n²，即 (Im ρ)² = t_n²
    (8) 由 Im ρ≥0, t_n≥0（maassSpecParam_nonneg），得 Im ρ = t_n
    (9) 故 ρ = 1/2 + i·t_n，且 ζ(ρ)=0。 -/
theorem maass_param_to_zero (f : MollifiedTestFunction) :
    ∀ (n : ℕ), ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
      ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
  intro n
  have h_eq_dist : ∀ (g : MollifiedTestFunction), spectralSum g.toTestFunction = nontrivialZeroSum g.toTestFunction :=
    fun g => spectral_zero_equality g
  have h_supp_eq : distributionSupport spectralSum = distributionSupport nontrivialZeroSum :=
    distribution_equality_support spectralSum nontrivialZeroSum h_eq_dist
  have h_spec_supp := spectral_side_support
  have h_zero_supp := nontrivialZeroSum_support
  have h_set_eq : {x : ℝ | ∃ n : ℕ, x = 1 / 4 + (maassSpecParam n)^2} =
      {x : ℝ | ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ x = 1 / 4 + (ρ.im)^2} := by
    rw [←h_spec_supp, h_supp_eq, h_zero_supp]
  have h_main : (1 / 4 + (maassSpecParam n)^2) ∈ {x : ℝ | ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ x = 1 / 4 + (ρ.im)^2} := by
    have h_in_spec : (1 / 4 + (maassSpecParam n)^2) ∈ {x : ℝ | ∃ n : ℕ, x = 1 / 4 + (maassSpecParam n)^2} := by
      exact ⟨n, rfl⟩
    rw [h_set_eq]
    exact h_in_spec
  rcases h_main with ⟨ρ, hρ_zero, hρ_re1, hρ_re2, hρ_crit, hρ_im_nonneg, hρ_x⟩
  have h_t2 : (ρ.im)^2 = (maassSpecParam n)^2 := by linarith
  have h_tn_nonneg : 0 ≤ maassSpecParam n := maassSpecParam_nonneg n
  have h_im_eq : ρ.im = maassSpecParam n := by
    nlinarith [sq_nonneg (ρ.im - maassSpecParam n), sq_nonneg (ρ.im + maassSpecParam n)]
  have hρ_eq : ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
    apply Complex.ext <;> simp [hρ_crit, h_im_eq] <;> ring
  exact ⟨ρ, hρ_zero, hρ_eq⟩'''

axiom_block = '''/-- 正向谱-零点对应（公理，暂留，稍后在 distributionSupport 定义后降为 theorem）：
    每个 Maass 谱参数 t_n 对应 ζ 非平凡零点 ρ_n = 1/2 + i·t_n。 -/
axiom maass_param_to_zero (f : MollifiedTestFunction) :
    ∀ (n : ℕ), ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
      ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ)'''

if theorem_block in content:
    content = content.replace(theorem_block, axiom_block)
    print("恢复为 axiom 成功")
else:
    print("未找到 theorem block")

# 2. 在 zero_im_matches_maass_param 之后添加 theorem 版本
# 找到 zero_im_matches_maass_param 的结束位置
marker = "  exact ⟨n, h_t_eq⟩\n\n/-- 谱-零点支撑匹配（定理，由临界线+虚部匹配推出）："

theorem_to_add = '''  exact ⟨n, h_t_eq⟩

/-- 正向谱-零点对应（定理，由分布支撑比较推出）：
    每个 Maass 谱参数 t_n 对应 ζ 非平凡零点 ρ_n = 1/2 + i·t_n。
    证明与 zero_im_matches_maass_param 对称。 -/
theorem maass_param_to_zero (f : MollifiedTestFunction) :
    ∀ (n : ℕ), ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
      ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
  intro n
  have h_eq_dist : ∀ (g : MollifiedTestFunction), spectralSum g.toTestFunction = nontrivialZeroSum g.toTestFunction :=
    fun g => spectral_zero_equality g
  have h_supp_eq : distributionSupport spectralSum = distributionSupport nontrivialZeroSum :=
    distribution_equality_support spectralSum nontrivialZeroSum h_eq_dist
  have h_spec_supp := spectral_side_support
  have h_zero_supp := nontrivialZeroSum_support
  have h_set_eq : {x : ℝ | ∃ n : ℕ, x = 1 / 4 + (maassSpecParam n)^2} =
      {x : ℝ | ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ x = 1 / 4 + (ρ.im)^2} := by
    rw [←h_spec_supp, h_supp_eq, h_zero_supp]
  have h_main : (1 / 4 + (maassSpecParam n)^2) ∈ {x : ℝ | ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ x = 1 / 4 + (ρ.im)^2} := by
    have h_in_spec : (1 / 4 + (maassSpecParam n)^2) ∈ {x : ℝ | ∃ n : ℕ, x = 1 / 4 + (maassSpecParam n)^2} := by
      exact ⟨n, rfl⟩
    rw [h_set_eq]
    exact h_in_spec
  rcases h_main with ⟨ρ, hρ_zero, hρ_re1, hρ_re2, hρ_crit, hρ_im_nonneg, hρ_x⟩
  have h_t2 : (ρ.im)^2 = (maassSpecParam n)^2 := by linarith
  have h_tn_nonneg : 0 ≤ maassSpecParam n := maassSpecParam_nonneg n
  have h_im_eq : ρ.im = maassSpecParam n := by
    nlinarith [sq_nonneg (ρ.im - maassSpecParam n), sq_nonneg (ρ.im + maassSpecParam n)]
  have hρ_eq : ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
    apply Complex.ext <;> simp [hρ_crit, h_im_eq] <;> ring
  exact ⟨ρ, hρ_zero, hρ_eq⟩

/-- 谱-零点支撑匹配（定理，由临界线+虚部匹配推出）：'''

if marker in content:
    content = content.replace(marker, theorem_to_add)
    print("添加 theorem 成功")
else:
    print("未找到 marker")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print(f"总行数: {len(content.splitlines())}")
