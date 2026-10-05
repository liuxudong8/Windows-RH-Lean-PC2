f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# === 修改5: delta_trace_zero_correspondence 简化 ===
old5 = """/-- Delta 函数的迹等式-零点对应（定理，由结构分解+单点局部化+反证法推出）：
    对谱点 n 的 delta 磨光函数 δ_n，由 spectral_zero_equality 推出
    ζ 在 ρ=1/2+i·t_n 处有零点。

    证明（反证法）：
    (1) delta_melin_single_point_localization 给出 δ_n 满足谱点条件、
        Mellin 局部化、平凡贡献为零
    (2) spectralSum(δ_n) = 1（谱点条件）
    (3) 由 spectral_zero_equality，zetaZeroSide(δ_n) = 1
    (4) 由 zetaZeroSide_structure，zetaZeroSide(δ_n) = nontrivialZeroSum(δ_n) + trivialZeroContribution(δ_n)
    (5) trivialZeroContribution(δ_n) = 0，故 nontrivialZeroSum(δ_n) = 1
    (6) 反证：假设 s₀ = 1/2+i·t_n 不是零点
    (7) 由 Mellin 局部化，所有非平凡零点 ρ ≠ s₀ 处 melinTransform δ_n ρ = 0
    (8) 因 s₀ 不是零点，nontrivialZeroSum(δ_n) = 0，与 (5) 矛盾
    (9) 故 s₀ 是零点 -/
theorem delta_trace_zero_correspondence (f : MollifiedTestFunction) :
    ∀ (n : ℕ),
      (∀ (k : ℕ), k = n → f.toTestFunction.eval (specDiscM k) = 1) →
      (∀ (k : ℕ), k ≠ n → f.toTestFunction.eval (specDiscM k) = 0) →
      ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
        ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
  intro n h1 h2
  rcases delta_melin_single_point_localization n with ⟨δ, hδ1, hδ2, hδ_melin, hδ_triv⟩
  have h_spec_sum : spectralSum δ.toTestFunction = 1 :=
    spectralSum_delta_eq_one δ.toTestFunction n hδ1 hδ2
  have h_zero_eq : zetaZeroSide δ.toTestFunction = spectralSum δ.toTestFunction :=
    (spectral_zero_equality δ).symm
  have h_zeta_one : zetaZeroSide δ.toTestFunction = 1 := by
    rw [h_zero_eq, h_spec_sum]
  have h_struct : zetaZeroSide δ.toTestFunction =
      nontrivialZeroSum δ.toTestFunction + trivialZeroContribution δ.toTestFunction :=
    rfl
  have h_nontriv_one : nontrivialZeroSum δ.toTestFunction = 1 := by
    rw [h_struct] at h_zeta_one
    rw [hδ_triv] at h_zeta_one
    simpa using h_zeta_one"""

new5 = """/-- Delta 函数的迹等式-零点对应（定理，由结构分解+单点局部化+反证法推出）：
    对谱点 n 的 delta 磨光函数 δ_n，由 spectral_zero_equality 推出
    ζ 在 ρ=1/2+i·t_n 处有零点。

    证明（反证法）：
    (1) delta_melin_single_point_localization 给出 δ_n 满足谱点条件、Mellin 局部化
    (2) spectralSum(δ_n) = 1（谱点条件）
    (3) 由 spectral_zero_equality，nontrivialZeroSum(δ_n) = spectralSum(δ_n) = 1
    (4) 反证：假设 s₀ = 1/2+i·t_n 不是零点
    (5) 由 Mellin 局部化，所有非平凡零点 ρ ≠ s₀ 处 melinTransform δ_n ρ = 0
    (6) 因 s₀ 不是零点，nontrivialZeroSum(δ_n) = 0，与 (3) 矛盾
    (7) 故 s₀ 是零点 -/
theorem delta_trace_zero_correspondence (f : MollifiedTestFunction) :
    ∀ (n : ℕ),
      (∀ (k : ℕ), k = n → f.toTestFunction.eval (specDiscM k) = 1) →
      (∀ (k : ℕ), k ≠ n → f.toTestFunction.eval (specDiscM k) = 0) →
      ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
        ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
  intro n h1 h2
  rcases delta_melin_single_point_localization n with ⟨δ, hδ1, hδ2, hδ_melin, hδ_triv⟩
  have h_spec_sum : spectralSum δ.toTestFunction = 1 :=
    spectralSum_delta_eq_one δ.toTestFunction n hδ1 hδ2
  have h_nontriv_one : nontrivialZeroSum δ.toTestFunction = 1 := by
    have h_eq : spectralSum δ.toTestFunction = nontrivialZeroSum δ.toTestFunction :=
      spectral_zero_equality δ
    rw [h_eq] at h_spec_sum
    exact h_spec_sum"""

content = content.replace(old5, new5, 1)

# === 修改6: mollified_spectral_preserving_perturbation 结论改为 nontrivialZeroSum ===
old6 = """/-- 磨光函数的谱点保持扰动（定理，由局部化+分离推出）：
    对任意非临界线零点 ρ，存在两个磨光函数 f₁, f₂，使得：
    (1) 它们在所有谱点上取值相同
    (2) zetaZeroSide(f₁) ≠ zetaZeroSide(f₂)

    证明：
    (1) mollified_melin_separation 给出 f₁,f₂ 满足谱点相同、
        其他零点 Melin 相同、成对零点 Melin 和不同
    (2) zero_side_melin_localization 给出：其他零点 Melin 相同时，
        zetaZeroSide(f₁)=zetaZeroSide(f₂) ↔ 成对零点 Melin 和相同
    (3) 成对零点 Melin 和不同，故 zetaZeroSide(f₁) ≠ zetaZeroSide(f₂) -/
theorem mollified_spectral_preserving_perturbation (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        zetaZeroSide f1.toTestFunction ≠ zetaZeroSide f2.toTestFunction := by
  intro hz hre1 hre2 hne
  rcases mollified_melin_separation ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_other, h_pair_ne, h_triv_eq⟩
  have h_loc := zero_side_melin_localization ρ hz hre1 hre2 hne f1.toTestFunction f2.toTestFunction h_other h_triv_eq
  have h_zero_ne : zetaZeroSide f1.toTestFunction ≠ zetaZeroSide f2.toTestFunction := by
    intro h_eq
    have h_pair_eq := h_loc.mp h_eq
    exact h_pair_ne h_pair_eq
  exact ⟨f1, f2, h_pts, h_zero_ne⟩"""

new6 = """/-- 磨光函数的谱点保持扰动（定理，由局部化+分离推出）：
    对任意非临界线零点 ρ，存在两个磨光函数 f₁, f₂，使得：
    (1) 它们在所有谱点上取值相同
    (2) nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)

    证明：
    (1) mollified_melin_separation 给出 f₁,f₂ 满足谱点相同、
        其他零点 Melin 相同、成对零点 Melin 和不同、平凡贡献相同
    (2) zero_side_melin_localization 给出：其他零点 Melin 相同时，
        zetaZeroSide(f₁)=zetaZeroSide(f₂) ↔ 成对零点 Melin 和相同
    (3) 成对零点 Melin 和不同，故 zetaZeroSide(f₁) ≠ zetaZeroSide(f₂)
    (4) 由平凡贡献相同，zetaZeroSide 不同等价于 nontrivialZeroSum 不同 -/
theorem mollified_spectral_preserving_perturbation (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ n : ℕ, f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        nontrivialZeroSum f1.toTestFunction ≠ nontrivialZeroSum f2.toTestFunction := by
  intro hz hre1 hre2 hne
  rcases mollified_melin_separation ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_other, h_pair_ne, h_triv_eq⟩
  have h_loc := zero_side_melin_localization ρ hz hre1 hre2 hne f1.toTestFunction f2.toTestFunction h_other h_triv_eq
  have h_zero_ne : zetaZeroSide f1.toTestFunction ≠ zetaZeroSide f2.toTestFunction := by
    intro h_eq
    have h_pair_eq := h_loc.mp h_eq
    exact h_pair_ne h_pair_eq
  have h_nontriv_ne : nontrivialZeroSum f1.toTestFunction ≠ nontrivialZeroSum f2.toTestFunction := by
    intro h_eq
    have h_zz : zetaZeroSide f1.toTestFunction = zetaZeroSide f2.toTestFunction := by
      simp [zetaZeroSide, h_eq, h_triv_eq]
    exact h_zero_ne h_zz
  exact ⟨f1, f2, h_pts, h_nontriv_ne⟩"""

content = content.replace(old6, new6, 1)

# === 修改7: pair_contribution_sigma_dependent 结论改为 nontrivialZeroSum ===
old7 = """/-- 非临界线零点对的 σ 依赖性（定理，由谱点决定性+扰动公理推出）：
    对非临界线零点 ρ，存在 f₁, f₂ 使得
    spectralSum(f₁) = spectralSum(f₂) 且 zetaZeroSide(f₁) ≠ zetaZeroSide(f₂)。
    证明：
    (1) mollified_spectral_preserving_perturbation 给出 f₁, f₂ 在谱点取值相同且零点侧不同
    (2) spectral_sum_determined_by_points 从谱点取值相同推出 spectralSum(f₁)=spectralSum(f₂) -/
theorem pair_contribution_sigma_dependent (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f1 f2 : MollifiedTestFunction),
        spectralSum f1.toTestFunction = spectralSum f2.toTestFunction ∧
        zetaZeroSide f1.toTestFunction ≠ zetaZeroSide f2.toTestFunction := by
  intro hz hre1 hre2 hne
  rcases mollified_spectral_preserving_perturbation ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_zero_ne⟩
  have h_spec_eq : spectralSum f1.toTestFunction = spectralSum f2.toTestFunction :=
    spectral_sum_determined_by_points f1.toTestFunction f2.toTestFunction h_pts
  exact ⟨f1, f2, h_spec_eq, h_zero_ne⟩"""

new7 = """/-- 非临界线零点对的 σ 依赖性（定理，由谱点决定性+扰动公理推出）：
    对非临界线零点 ρ，存在 f₁, f₂ 使得
    spectralSum(f₁) = spectralSum(f₂) 且 nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)。
    证明：
    (1) mollified_spectral_preserving_perturbation 给出 f₁, f₂ 在谱点取值相同且非平凡零点侧不同
    (2) spectral_sum_determined_by_points 从谱点取值相同推出 spectralSum(f₁)=spectralSum(f₂) -/
theorem pair_contribution_sigma_dependent (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f1 f2 : MollifiedTestFunction),
        spectralSum f1.toTestFunction = spectralSum f2.toTestFunction ∧
        nontrivialZeroSum f1.toTestFunction ≠ nontrivialZeroSum f2.toTestFunction := by
  intro hz hre1 hre2 hne
  rcases mollified_spectral_preserving_perturbation ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_nontriv_ne⟩
  have h_spec_eq : spectralSum f1.toTestFunction = spectralSum f2.toTestFunction :=
    spectral_sum_determined_by_points f1.toTestFunction f2.toTestFunction h_pts
  exact ⟨f1, f2, h_spec_eq, h_nontriv_ne⟩"""

content = content.replace(old7, new7, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: modifications 5-7')
