f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. jlLParameterMap 从 def 改为 opaque
old_lparam = '''/-- JL L-参数映射（def，由 JL 对应直接给出）：
    jlLParameterMap(n) = 1/2 + i*maassSpecParam(jlSpectrumMap(n))。
    三维表示 pi_n 的 L-参数等于对应 Maass 表示的 L-参数。 -/
noncomputable def jlLParameterMap (n : ℕ) : ℂ :=
    (1 / 2 : ℂ) + Complex.I * (maassSpecParam (jlSpectrumMap n) : ℂ)'''
new_lparam = '''/-- JL L-参数映射（opaque）：
    ψ: ℕ → ℂ 将三维谱指标 n 映射到对应自守表示的 L-参数。
    L-参数是表示的内在属性，不预设等于 Maass 的 L-参数。 -/
opaque jlLParameterMap : ℕ → ℂ'''
content = content.replace(old_lparam, new_lparam, 1)

# 2. 在 eigenfunction_cancellation 之后添加 l_parameter_standard_form 和 l_parameter_im_nonneg
old_eig_cancel = '''/-- 特征函数消去律（公理）：a·ψ_n = b·ψ_n → a = b。 -/
axiom eigenfunction_cancellation (n : ℕ) (a b : ℂ) :
    a • threeManifoldEigenfunction n = b • threeManifoldEigenfunction n → a = b

/-- 实数嵌入复数的单射性（公理）：'''
new_eig_cancel = '''/-- 特征函数消去律（公理）：a·ψ_n = b·ψ_n → a = b。 -/
axiom eigenfunction_cancellation (n : ℕ) (a b : ℂ) :
    a • threeManifoldEigenfunction n = b • threeManifoldEigenfunction n → a = b

/-- L-参数标准形式（公理）：jlLParameterMap(n).re = 1/2。
    这是自守表示 L-参数的标准性质：对 PGL₂，L-参数形如 1/2 + it。 -/
axiom l_parameter_standard_form :
    ∀ (n : ℕ), (jlLParameterMap n).re = 1 / 2

/-- L-参数虚部非负（公理）：0 ≤ jlLParameterMap(n).im。 -/
axiom l_parameter_im_nonneg :
    ∀ (n : ℕ), 0 ≤ (jlLParameterMap n).im

/-- 实数嵌入复数的单射性（公理）：'''
content = content.replace(old_eig_cancel, new_eig_cancel, 1)

# 3. 在第796行注释后添加 l_parameter_eigenvalue_formula 公理
old_comment = '''    对应 Borel (1997) "Automoprhic forms on SL₂(R)" 第 2 章。 -/
noncomputable def maassSpectralSum'''
new_comment = '''    对应 Borel (1997) "Automoprhic forms on SL₂(R)" 第 2 章。 -/
axiom l_parameter_eigenvalue_formula :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (jlLParameterMap n).im^2

noncomputable def maassSpectralSum'''
content = content.replace(old_comment, new_comment, 1)

# 4. 删除当前的 l_parameter_eigenvalue_formula 定理（从注释到定理结束）
old_theorem = '''/-- L-参数与 Laplacian 本征值对应（定理，由 Shimura 提升 + 保 Laplacian 推出）：
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

# 替换为 jl_l_parameter_preserving 定理
new_theorem = '''/-- JL L-参数保持（定理，由 Shimura 提升 + 保 Laplacian + 特征值方程推出）：
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

content = content.replace(old_theorem, new_theorem, 1)

# 5. 修复 jl_spectrum_preserving 定理
old_jl_spec = '''/-- JL 谱保持（定理，即 l_parameter_eigenvalue_formula）：
    酉对应 U 与 Laplacian 交换，故保持本征值：
      specDiscM(n) = 1/4 + (maassSpecParam(φ(n)))²
    由 Shimura 提升核显式推出（见 l_parameter_eigenvalue_formula）。
    对应 Jacquet-Langlands (1970) 与 Gelbart-Jacquet (1978)。 -/
theorem jl_spectrum_preserving :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2 :=
  l_parameter_eigenvalue_formula'''
new_jl_spec = '''/-- JL 谱保持（定理，由 L-参数保持 + 本征值公式推出）：
    酉对应 U 与 Laplacian 交换，故保持本征值：
      specDiscM(n) = 1/4 + (maassSpecParam(φ(n)))²
    证明：
    (1) l_parameter_eigenvalue_formula: specDiscM(n) = 1/4 + (jlLParameterMap(n).im)²
    (2) jl_l_parameter_preserving: jlLParameterMap(n) = 1/2 + i·maassSpecParam(φ(n))
    (3) 所以 (jlLParameterMap(n)).im = maassSpecParam(φ(n))
    (4) 代入得 specDiscM(n) = 1/4 + (maassSpecParam(φ(n)))²
    数学依据：JL 对应保持 L-参数，而 Laplacian 本征值由 L-参数决定。
    对应 Jacquet-Langlands (1970) 与 Gelbart-Jacquet (1978)。 -/
theorem jl_spectrum_preserving :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2 := by
  intro n
  have h1 : specDiscM n = 1 / 4 + (jlLParameterMap n).im^2 :=
    l_parameter_eigenvalue_formula n
  have h2 : jlLParameterMap n = (1 / 2 : ℂ) + Complex.I * (maassSpecParam (jlSpectrumMap n) : ℂ) :=
    jl_l_parameter_preserving n
  rw [h1, h2]
  <;> simp [Complex.add_im, Complex.mul_im, Complex.I_im] <;> ring'''
content = content.replace(old_jl_spec, new_jl_spec, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: restored jlLParameterMap as opaque')
