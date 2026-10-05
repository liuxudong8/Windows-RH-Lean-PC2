f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 删除 jl_l_parameter_preserving 定理（从第831行注释到第893行）
old_jl = '''/-- JL L-参数保持（定理，由 Shimura 提升 + 保 Laplacian + 特征值方程推出）：
    JL 对应保持 L-参数：三维表示 π_n 的 L-参数等于 Maass 表示 π'_{φ(n)} 的 L-参数。
    具体地，jlLParameterMap(n) = 1/2 + i·maassSpecParam(φ(n))。
    证明（从 Shimura 提升核显式推出）：
    (1) shimuraLift_eigenfunction_correspondence: U(φ_k) = ψ_n, k=jlSpectrumMap(n)
    (2) shimuraLift_commutes_laplacian: Δ_M(U φ_k) = U(Δ_X φ_k)
    (3) maass_eigenvalue_equation: Δ_X φ_k = (1/4+t_k²)φ_k
    (4) shimuraLift_linear: U((1/4+t_k²)φ_k) = (1/4+t_k²)U(φ_k) = (1/4+t_k²)ψ_n
    (5) threeManifold_eigenvalue_equation: Δ_M ψ_n = specDiscM(n)ψ_n
    (6) eigenfunction_cancellation: specDiscM(n) = 1/4+t_k²
    (7) l_parameter_eigenvalue_formula: specDiscM(n) = 1/4+(jlLParameterMap(n).im)²
    (8) 故 (jlLParameterMap(n).im)² = t_k²，由非负性得 jlLParameterMap(n).im = t_k
    (9) l_parameter_standard_form: jlLParameterMap(n).re = 1/2
    (10) 故 jlLParameterMap(n) = 1/2 + i·t_k = 1/2 + i·maassSpecParam(jlSpectrumMap(n))
    这把 JL 对应从"表示论存在性断言"替换为"Shimura 提升核分析断言"。 -/
theorem jl_l_parameter_preserving :
    ∀ (n : ℕ), jlLParameterMap n = (1 / 2 : ℂ) + Complex.I * (maassSpecParam (jlSpectrumMap n) : ℂ) := by
  intro n
  let k := jlSpectrumMap n
  set a : ℂ := ((1 / 4 + (maassSpecParam k)^2 : ℝ) : ℂ) with ha
  have h1 : shimuraLift (maassEigenfunction k) = threeManifoldEigenfunction n :=
    shimuraLift_eigenfunction_correspondence n
  have h2 : shimuraLift (laplacian_X (maassEigenfunction k)) =
           laplacian_M (shimuraLift (maassEigenfunction k)) :=
    shimuraLift_commutes_laplacian (maassEigenfunction k)
  have h3 : laplacian_X (maassEigenfunction k) = a • maassEigenfunction k := by
    simpa [ha] using maass_eigenvalue_equation k
  have h4 : shimuraLift (a • maassEigenfunction k) = a • shimuraLift (maassEigenfunction k) :=
    shimuraLift_linear a (maassEigenfunction k)
  have h5 : laplacian_M (threeManifoldEigenfunction n) =
           (specDiscM n : ℂ) • threeManifoldEigenfunction n :=
    threeManifold_eigenvalue_equation n
  have h_step1 : shimuraLift (laplacian_X (maassEigenfunction k)) = a • threeManifoldEigenfunction n := by
    calc
      shimuraLift (laplacian_X (maassEigenfunction k))
        = shimuraLift (a • maassEigenfunction k) := by rw [h3]
      _ = a • shimuraLift (maassEigenfunction k) := h4
      _ = a • threeManifoldEigenfunction n := by rw [h1]
  have h_step2 : laplacian_M (threeManifoldEigenfunction n) = a • threeManifoldEigenfunction n := by
    calc
      laplacian_M (threeManifoldEigenfunction n)
        = laplacian_M (shimuraLift (maassEigenfunction k)) := by rw [h1]
      _ = shimuraLift (laplacian_X (maassEigenfunction k)) := h2.symm
      _ = a • threeManifoldEigenfunction n := h_step1
  have h6 : a • threeManifoldEigenfunction n = (specDiscM n : ℂ) • threeManifoldEigenfunction n := by
    rw [←h_step2, h5]
  have h7 : a = (specDiscM n : ℂ) :=
    eigenfunction_cancellation n a (specDiscM n : ℂ) h6
  have h7_simp : (1 / 4 + (maassSpecParam k)^2 : ℝ) = (specDiscM n : ℝ) :=
    real_complex_inj (1 / 4 + (maassSpecParam k)^2) (specDiscM n) (by simpa [ha] using h7)
  have h_spec : specDiscM n = 1 / 4 + (maassSpecParam k)^2 := h7_simp.symm
  have h_lparam : specDiscM n = 1 / 4 + (jlLParameterMap n).im^2 :=
    l_parameter_eigenvalue_formula n
  have h_im_sq : (jlLParameterMap n).im^2 = (maassSpecParam k)^2 := by
    linarith [h_spec, h_lparam]
  have h_im_nonneg : 0 ≤ (jlLParameterMap n).im := l_parameter_im_nonneg n
  have h_k_nonneg : 0 ≤ maassSpecParam k := maassSpecParam_nonneg k
  have h_im : (jlLParameterMap n).im = maassSpecParam k := by
    nlinarith
  have h_re : (jlLParameterMap n).re = 1 / 2 := l_parameter_standard_form n
  apply Complex.ext
  · simpa using h_re
  · simpa using h_im

'''

# 替换为 l_parameter_eigenvalue_formula 定理（由 Shimura 提升证明）
new_jl = '''/-- L-参数与 Laplacian 本征值对应（定理，由 Shimura 提升 + 保 Laplacian 推出）：
    specDiscM(n) = 1/4 + (maassSpecParam(jlSpectrumMap(n)))²。
    证明：
    (1) shimuraLift_eigenfunction_correspondence: U(φ_k) = ψ_n, k=jlSpectrumMap(n)
    (2) shimuraLift_commutes_laplacian: Δ_M(U φ_k) = U(Δ_X φ_k)
    (3) maass_eigenvalue_equation: Δ_X φ_k = (1/4+t_k²)φ_k
    (4) threeManifold_eigenvalue_equation: Δ_M ψ_n = specDiscM(n)ψ_n
    (5) eigenfunction_cancellation: specDiscM(n) = 1/4+t_k²
    这把 JL 对应从"表示论存在性断言"替换为"Shimura 提升核分析断言"。 -/
theorem l_parameter_eigenvalue_formula :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2 := by
  intro n
  let k := jlSpectrumMap n
  set a : ℂ := ((1 / 4 + (maassSpecParam k)^2 : ℝ) : ℂ) with ha
  have h1 : shimuraLift (maassEigenfunction k) = threeManifoldEigenfunction n :=
    shimuraLift_eigenfunction_correspondence n
  have h2 : shimuraLift (laplacian_X (maassEigenfunction k)) =
           laplacian_M (shimuraLift (maassEigenfunction k)) :=
    shimuraLift_commutes_laplacian (maassEigenfunction k)
  have h3 : laplacian_X (maassEigenfunction k) = a • maassEigenfunction k := by
    simpa [ha] using maass_eigenvalue_equation k
  have h4 : shimuraLift (a • maassEigenfunction k) = a • shimuraLift (maassEigenfunction k) :=
    shimuraLift_linear a (maassEigenfunction k)
  have h5 : laplacian_M (threeManifoldEigenfunction n) =
           (specDiscM n : ℂ) • threeManifoldEigenfunction n :=
    threeManifold_eigenvalue_equation n
  have h_step1 : shimuraLift (laplacian_X (maassEigenfunction k)) = a • threeManifoldEigenfunction n := by
    calc
      shimuraLift (laplacian_X (maassEigenfunction k))
        = shimuraLift (a • maassEigenfunction k) := by rw [h3]
      _ = a • shimuraLift (maassEigenfunction k) := h4
      _ = a • threeManifoldEigenfunction n := by rw [h1]
  have h_step2 : laplacian_M (threeManifoldEigenfunction n) = a • threeManifoldEigenfunction n := by
    calc
      laplacian_M (threeManifoldEigenfunction n)
        = laplacian_M (shimuraLift (maassEigenfunction k)) := by rw [h1]
      _ = shimuraLift (laplacian_X (maassEigenfunction k)) := h2.symm
      _ = a • threeManifoldEigenfunction n := h_step1
  have h6 : a • threeManifoldEigenfunction n = (specDiscM n : ℂ) • threeManifoldEigenfunction n := by
    rw [←h_step2, h5]
  have h7 : a = (specDiscM n : ℂ) :=
    eigenfunction_cancellation n a (specDiscM n : ℂ) h6
  have h7_simp : (1 / 4 + (maassSpecParam k)^2 : ℝ) = (specDiscM n : ℝ) :=
    real_complex_inj (1 / 4 + (maassSpecParam k)^2) (specDiscM n) (by simpa [ha] using h7)
  exact h7_simp.symm

'''

content = content.replace(old_jl, new_jl, 1)

# 删除原来的 l_parameter_eigenvalue_formula 公理（在第812-820行附近）
old_axiom = '''/-- L-参数与 Laplacian 本征值对应（公理）：
    specDiscM(n) = 1/4 + (maassSpecParam(jlSpectrumMap(n)))²。
    这是自守表示理论的标准结果：Casimir 本征值由 L-参数决定。
    对应 Borel (1997) "Automoprhic forms on SL₂(R)" 第 2 章。 -/
axiom l_parameter_eigenvalue_formula :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2
'''
content = content.replace(old_axiom, '', 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: l_parameter_eigenvalue_formula -> theorem')
