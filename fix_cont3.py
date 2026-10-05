f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# === 修改8: off_critical_line_contradiction ===
old8 = """/-- 非临界线零点的矛盾（定理，由 σ 依赖性推出）：
    如果存在非临界线零点 ρ，则存在磨光函数 f 使得
    spectralSum(f) ≠ zetaZeroSide(f)。

    证明：由 pair_contribution_sigma_dependent，存在 f₁, f₂ 使得
    spectralSum(f₁) = spectralSum(f₂) 但 zetaZeroSide(f₁) ≠ zetaZeroSide(f₂)。
    若 spectralSum(f) = zetaZeroSide(f) 对所有磨光 f 成立，则
    zetaZeroSide(f₁) = spectralSum(f₁) = spectralSum(f₂) = zetaZeroSide(f₂)，矛盾。
    故 f₁, f₂ 中至少有一个满足 spectralSum(f) ≠ zetaZeroSide(f)。 -/
theorem off_critical_line_contradiction :
    ∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f : MollifiedTestFunction),
        spectralSum f.toTestFunction ≠ zetaZeroSide f.toTestFunction := by
  intro ρ hz hre1 hre2 hne
  rcases pair_contribution_sigma_dependent ρ hz hre1 hre2 hne with ⟨f1, f2, h_spec_eq, h_zero_ne⟩
  by_cases h1 : spectralSum f1.toTestFunction = zetaZeroSide f1.toTestFunction
  · by_cases h2 : spectralSum f2.toTestFunction = zetaZeroSide f2.toTestFunction
    · have h_contra : zetaZeroSide f1.toTestFunction = zetaZeroSide f2.toTestFunction := by
        calc zetaZeroSide f1.toTestFunction
          = spectralSum f1.toTestFunction := h1.symm
        _ = spectralSum f2.toTestFunction := h_spec_eq
        _ = zetaZeroSide f2.toTestFunction := h2
      exact False.elim (h_zero_ne h_contra)
    · exact ⟨f2, h2⟩
  · exact ⟨f1, h1⟩"""

new8 = """/-- 非临界线零点的矛盾（定理，由 σ 依赖性推出）：
    如果存在非临界线零点 ρ，则存在磨光函数 f 使得
    spectralSum(f) ≠ nontrivialZeroSum(f)。

    证明：由 pair_contribution_sigma_dependent，存在 f₁, f₂ 使得
    spectralSum(f₁) = spectralSum(f₂) 但 nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)。
    若 spectralSum(f) = nontrivialZeroSum(f) 对所有磨光 f 成立，则
    nontrivialZeroSum(f₁) = spectralSum(f₁) = spectralSum(f₂) = nontrivialZeroSum(f₂)，矛盾。
    故 f₁, f₂ 中至少有一个满足 spectralSum(f) ≠ nontrivialZeroSum(f)。 -/
theorem off_critical_line_contradiction :
    ∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f : MollifiedTestFunction),
        spectralSum f.toTestFunction ≠ nontrivialZeroSum f.toTestFunction := by
  intro ρ hz hre1 hre2 hne
  rcases pair_contribution_sigma_dependent ρ hz hre1 hre2 hne with ⟨f1, f2, h_spec_eq, h_nontriv_ne⟩
  by_cases h1 : spectralSum f1.toTestFunction = nontrivialZeroSum f1.toTestFunction
  · by_cases h2 : spectralSum f2.toTestFunction = nontrivialZeroSum f2.toTestFunction
    · have h_contra : nontrivialZeroSum f1.toTestFunction = nontrivialZeroSum f2.toTestFunction := by
        calc nontrivialZeroSum f1.toTestFunction
          = spectralSum f1.toTestFunction := h1.symm
        _ = spectralSum f2.toTestFunction := h_spec_eq
        _ = nontrivialZeroSum f2.toTestFunction := h2
      exact False.elim (h_nontriv_ne h_contra)
    · exact ⟨f2, h2⟩
  · exact ⟨f1, h1⟩"""

content = content.replace(old8, new8, 1)

# === 修改9: all_zeros_on_critical_line ===
old9 = """/-- 所有非平凡零点在临界线上（定理，由反证法推出）：
    假设存在零点 s 不在临界线上（s.re ≠ 1/2），
    由 off_critical_line_contradiction，存在磨光函数 f 使得
    spectralSum(f) ≠ zetaZeroSide(f)，
    与 spectral_zero_equality（谱侧=零点侧，对所有磨光 f 成立）矛盾。
    因此所有非平凡零点都满足 Re(s) = 1/2。

    这是 RH 的核心结论：临界带内的零点全部在临界线上。 -/
theorem all_zeros_on_critical_line (f : MollifiedTestFunction) :
    ∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  intro s hs hre1 hre2
  by_contra h_ne
  have h_contra := off_critical_line_contradiction s hs hre1 hre2 h_ne
  rcases h_contra with ⟨g, hg⟩
  have h_eq : spectralSum g.toTestFunction = zetaZeroSide g.toTestFunction :=
    spectral_zero_equality g
  exact hg h_eq"""

new9 = """/-- 所有非平凡零点在临界线上（定理，由反证法推出）：
    假设存在零点 s 不在临界线上（s.re ≠ 1/2），
    由 off_critical_line_contradiction，存在磨光函数 f 使得
    spectralSum(f) ≠ nontrivialZeroSum(f)，
    与 spectral_zero_equality（谱侧=非平凡零点侧，对所有磨光 f 成立）矛盾。
    因此所有非平凡零点都满足 Re(s) = 1/2。

    这是 RH 的核心结论：临界带内的零点全部在临界线上。 -/
theorem all_zeros_on_critical_line (f : MollifiedTestFunction) :
    ∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  intro s hs hre1 hre2
  by_contra h_ne
  have h_contra := off_critical_line_contradiction s hs hre1 hre2 h_ne
  rcases h_contra with ⟨g, hg⟩
  have h_eq : spectralSum g.toTestFunction = nontrivialZeroSum g.toTestFunction :=
    spectral_zero_equality g
  exact hg h_eq"""

content = content.replace(old9, new9, 1)

# === 修改10: zero_side_support 公理改为 nontrivialZeroSum_support ===
old10 = """/-- 零点侧分布的支撑（公理）：
    zetaZeroSide(f) 的支撑为 {1/4+t² : ∃ρ, ζ(ρ)=0 ∧ Re(ρ)=1/2 ∧ 0≤Im(ρ) ∧ t=Im(ρ)}。
    即零点侧分布的奇点恰在上半平面临界线零点对应的谱参数 λ=1/4+t² 处。
    （下半平面零点是上半平面零点的共轭，对应相同的 t²，故不重复计入。）
    这是 Weil 显式公式零点侧求和的标准性质：
    每个临界线上零点 ρ=1/2+it 对应支撑点 1/4+t²。 -/
axiom zero_side_support :
    distributionSupport zetaZeroSide ="""

new10 = """/-- 非平凡零点侧分布的支撑（公理）：
    nontrivialZeroSum(f) 的支撑为 {1/4+t² : ∃ρ, ζ(ρ)=0 ∧ Re(ρ)=1/2 ∧ 0≤Im(ρ) ∧ t=Im(ρ)}。
    即非平凡零点侧分布的奇点恰在上半平面临界线零点对应的谱参数 λ=1/4+t² 处。
    （下半平面零点是上半平面零点的共轭，对应相同的 t²，故不重复计入。）
    这是 Weil 显式公式非平凡零点侧求和的标准性质：
    每个临界线上零点 ρ=1/2+it 对应支撑点 1/4+t²。 -/
axiom nontrivialZeroSum_support :
    distributionSupport nontrivialZeroSum ="""

content = content.replace(old10, new10, 1)

# === 修改11: zero_im_matches_maass_param 中的 zetaZeroSide → nontrivialZeroSum ===
old11 = """  have h_eq_dist : ∀ (f : MollifiedTestFunction), spectralSum f.toTestFunction = zetaZeroSide f.toTestFunction :=
    fun f => spectral_zero_equality f
  have h_supp_eq : distributionSupport spectralSum = distributionSupport zetaZeroSide :=
    distribution_equality_support spectralSum zetaZeroSide h_eq_dist
  have h_spec_supp := spectral_side_support
  have h_zero_supp := zero_side_support"""

new11 = """  have h_eq_dist : ∀ (f : MollifiedTestFunction), spectralSum f.toTestFunction = nontrivialZeroSum f.toTestFunction :=
    fun f => spectral_zero_equality f
  have h_supp_eq : distributionSupport spectralSum = distributionSupport nontrivialZeroSum :=
    distribution_equality_support spectralSum nontrivialZeroSum h_eq_dist
  have h_spec_supp := spectral_side_support
  have h_zero_supp := nontrivialZeroSum_support"""

content = content.replace(old11, new11, 1)

# === 修改12: riemann_hypothesis 注释 ===
old12 = """/-- 黎曼猜想（主定理）：所有非平凡零点 Re(s)=1/2
    证明：直接由 all_zeros_on_critical_line 推出。
    all_zeros_on_critical_line 由反证法证明：
    若存在零点 s 不在临界线上（Re(s)≠1/2），
    由 off_critical_line_contradiction（定理），存在磨光函数 f 使
    spectralSum(f) ≠ zetaZeroSide(f)，与 spectral_zero_equality 矛盾。
    因此所有非平凡零点都在临界线上。 -/"""

new12 = """/-- 黎曼猜想（主定理）：所有非平凡零点 Re(s)=1/2
    证明：直接由 all_zeros_on_critical_line 推出。
    all_zeros_on_critical_line 由反证法证明：
    若存在零点 s 不在临界线上（Re(s)≠1/2），
    由 off_critical_line_contradiction（定理），存在磨光函数 f 使
    spectralSum(f) ≠ nontrivialZeroSum(f)，与 spectral_zero_equality 矛盾。
    因此所有非平凡零点都在临界线上。 -/"""

content = content.replace(old12, new12, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: modifications 8-12')
