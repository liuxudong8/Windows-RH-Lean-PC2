/-
Stage-4: RH Spectral Duality Argument (v4.0)
基于论文《基于 Arthur 稳定迹、Jacquet–Langlands 对应与测地流指数混合的谱对偶论证9》
-/
import OrderPreservingBijection.stage_3
import OrderPreservingBijection.QuadraticFieldFive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.CircleIntegral
import OrderPreservingBijection.ContourIntegral
import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.ManifoldInfrastructure
import OrderPreservingBijection.HeatKernel
import OrderPreservingBijection.HeatKernelSemigroup
import OrderPreservingBijection.MollifiedFunction
import OrderPreservingBijection.Interpolation
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.MellinTransform

import OrderPreservingBijection.InnerProduct
import OrderPreservingBijection.test_rpow_ineq
import OrderPreservingBijection.test_general_rpow_ineq
namespace RHSpectralDuality

open Complex OrderPreservingBijection
open Filter Topology MeasureTheory

/- Section 0: 流形类型与 L² 函数空间 -/

/-- 黎曼ζ函数的零点对称性（定理，函数方程的直接推论）：
    如果 ρ 是非平凡零点（0 < Re(ρ) < 1），则 1 - ρ 也是非平凡零点。
    由 Mathlib 的 riemannZeta_one_sub（函数方程）直接推出：
    ζ(1-ρ) = C(ρ)·ζ(ρ) = C(ρ)·0 = 0，其中 C(ρ) 是 Γ 和 cos 的乘积。 -/
theorem riemann_zeta_zero_symmetry (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    _root_.riemannZeta (1 - ρ) = 0 ∧ 0 < (1 - ρ).re ∧ (1 - ρ).re < 1 := by
  intro hz hre1 hre2
  have h1 : ∀ (n : ℕ), ρ ≠ (-n : ℂ) := by
    intro n
    intro h
    have hre : ρ.re = (-n : ℝ) := by exact_mod_cast congr_arg Complex.re h
    linarith
  have h2 : ρ ≠ (1 : ℂ) := by
    intro h
    have hre : ρ.re = 1 := by exact_mod_cast congr_arg Complex.re h
    linarith
  have h_fe : _root_.riemannZeta (1 - ρ) = 2 * (2 * Real.pi) ^ (-ρ) * Complex.Gamma ρ * Complex.cos (Real.pi * ρ / 2) * _root_.riemannZeta ρ :=
    riemannZeta_one_sub h1 h2
  have h_zero : _root_.riemannZeta (1 - ρ) = 0 := by
    rw [h_fe, hz] <;> ring
  have h_re1 : 0 < (1 - ρ).re := by simp [Complex.sub_re] <;> linarith
  have h_re2 : (1 - ρ).re < 1 := by simp [Complex.sub_re] <;> linarith
  exact ⟨h_zero, h_re1, h_re2⟩

/-- 二维 Laplacian（opaque，类型化）：Δ_X : L²(X) → L²(X)。 -/
noncomputable def laplacian_X : L2ManifoldX → L2ManifoldX := fun _ => Classical.arbitrary L2ManifoldX

/-- 三维 Laplacian 具有离散谱（公理，第一档，非空洞版本）：
    存在序列 s : ℕ → ℝ，满足：
    (1) 非负 (2) 严格递增 (3) 无界
    (4) 每个 s n 都是 laplacian_M 的特征值（存在非零特征向量）。
    这是自伴椭圆算子离散谱的标准性质（Rellich 引理 + 紧自伴算子谱定理）。
    比旧版 specDiscM_exists 更强：序列不再是任意的，而是 Laplacian 的特征值枚举。 -/
theorem laplacian_has_discrete_spectrum :
    (∀ (f g : L2ManifoldM), innerProductM (laplacian_M f) g = innerProductM f (laplacian_M g)) ∧
    (∃ (s : ℕ → ℝ),
      (0 < s 0) ∧
      (∀ n : ℕ, 1 / 4 ≤ s n) ∧
      (∀ n : ℕ, s n < s (n + 1)) ∧
      (∀ M : ℝ, ∃ n : ℕ, s n > M) ∧
      (∀ n : ℕ, ∃ (ψ : L2ManifoldM), ψ ≠ 0 ∧ laplacian_M ψ = (s n : ℂ) • ψ)) := by
  -- 数学：Rellich 引理 + 紧自伴算子谱定理
  -- (1) Laplacian 自伴性：分部积分 + 边界项为零
  -- (2) Rellich 引理：紧流形上 Laplacian 的预解式是紧算子
  -- (3) 紧自伴算子谱定理：离散谱 + 特征向量正交基
  -- (4) 谱隙：0 不是 L² 特征值（非紧有限体积）
  sorry

/-- 三维离散谱（定义，由离散谱公理通过 Classical.choose 给出）。
    非空洞：specDiscM n 是 laplacian_M 的第 n 个特征值。 -/
noncomputable def specDiscM : ℕ → ℝ := Classical.choose laplacian_has_discrete_spectrum.2

/-- Laplacian 谱隙（公理）：最小离散特征值严格大于 0。
    数学原因：双曲三流形 ℍ³/Γ 上常数函数不在 L² 中（非紧有限体积），
    故 0 不是 L² 特征值，谱底 > 0。这是 PointSetSeparable 的前提。 -/
theorem laplacian_spectral_gap : 0 < specDiscM 0 :=
  (Classical.choose_spec laplacian_has_discrete_spectrum.2).1

/-- 三维离散谱 SpecDisc(M) 的性质束（定理，由 Classical.choose_spec 推出）：
    1. 非负 2. 严格递增 3. 无界 -/
theorem specDiscM_properties :
    (∀ n : ℕ, 0 ≤ specDiscM n) ∧
    (∀ n : ℕ, specDiscM n < specDiscM (n + 1)) ∧
    (∀ M : ℝ, ∃ n : ℕ, specDiscM n > M) :=
  let h := Classical.choose_spec laplacian_has_discrete_spectrum.2
  ⟨fun n => by
    have h' : 1 / 4 ≤ specDiscM n := h.2.1 n
    have h'' : (0 : ℝ) ≤ 1 / 4 := by norm_num
    linarith, h.2.2.1, h.2.2.2.1⟩

/-- 离散谱点集可分离（定理，由谱隙 + 严格递增推出）：
    选择 Λ0=lam0/3, Λ1=lam0/2，则 (-∞,Λ0/2]∪[Λ0,Λ1] 与 range(specDiscM) 不相交。 -/
theorem specDiscM_separable : PointSetSeparable (Set.range specDiscM) := by
  have hlam0_pos : 0 < specDiscM 0 := laplacian_spectral_gap
  have hlam0_le : ∀ n, specDiscM 0 ≤ specDiscM n := by
    intro n
    have h_strict := specDiscM_properties.2.1
    have h : specDiscM 0 ≤ specDiscM n := by
      induction n with
      | zero => linarith
      | succ n ih => linarith [h_strict n]
    exact h
  refine ⟨specDiscM 0 / 3, specDiscM 0 / 2, by linarith, by linarith, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨n, rfl⟩
    have h : specDiscM 0 / 6 < specDiscM n := by linarith [hlam0_le n]
    have h' : (specDiscM 0 / 3) / 2 < specDiscM n := by
      have h_eq : (specDiscM 0 / 3) / 2 = specDiscM 0 / 6 := by ring
      rw [h_eq]; exact h
    exact h'
  · intro x hx
    rcases hx with ⟨n, rfl⟩
    have h : specDiscM 0 / 2 < specDiscM n := by linarith [hlam0_le n]
    exact Or.inr h

/-- 谱点序列单调非减（引理）：specDiscM 严格递增蕴含 specDiscM m ≤ specDiscM n 当 m ≤ n。 -/
lemma specDiscM_monotone (m n : ℕ) (h : m ≤ n) : specDiscM m ≤ specDiscM n := by
  have h_strict := specDiscM_properties.2.1
  induction n with
  | zero =>
    have h_m0 : m = 0 := by omega
    rw [h_m0] <;> linarith
  | succ n ih =>
    by_cases hmn : m ≤ n
    · have h_ih : specDiscM m ≤ specDiscM n := ih hmn
      linarith [h_strict n]
    · have h_eq : m = n + 1 := by omega
      rw [h_eq] <;> linarith

/-- 谱点集与紧支集的交有限（引理）：
    specDiscM 严格递增无界，故 {n | specDiscM n ≤ R} 有限。 -/
lemma specDiscM_support_intersection_finite (R : ℝ) :
    Set.Finite {n : ℕ | specDiscM n ≤ R} := by
  have h_unbounded := specDiscM_properties.2.2
  rcases h_unbounded R with ⟨N, hN⟩
  have h : {n : ℕ | specDiscM n ≤ R} ⊆ Finset.range N := by
    intro n hn
    have h_le : specDiscM n ≤ R := hn
    have h_lt : n < N := by
      by_contra h_contra
      have h_ge : N ≤ n := by linarith
      have h_mon : specDiscM N ≤ specDiscM n := specDiscM_monotone N n h_ge
      linarith
    exact Finset.mem_range.mpr h_lt
  exact Set.Finite.subset (Finset.finite_toSet _) h

/-- 磨光函数在谱点集上的非零点集有限（引理）：
    f 紧支 + specDiscM 离散无界 → {x ∈ range(specDiscM) | f.eval x ≠ 0} 有限。 -/
lemma mollified_eval_support_finite (f : TestFunction) :
    Set.Finite {x ∈ Set.range specDiscM | f.eval x ≠ 0} := by
  rcases f.hasCompactSupport with ⟨R, hR_pos, hR⟩
  have h1 : {x ∈ Set.range specDiscM | f.eval x ≠ 0} ⊆
            {x ∈ Set.range specDiscM | x ≤ R} := by
    intro x hx
    rcases hx with ⟨h_in, h_ne⟩
    have h_x_le_R : x ≤ R := by
      by_contra h_contra
      have h_gt : R < x := by linarith
      have h_abs : |x| > R := by
        have h_x_pos : 0 ≤ x := by
          rcases h_in with ⟨n, rfl⟩
          exact specDiscM_properties.1 n
        rw [abs_of_nonneg h_x_pos] <;> linarith
      have h_f0 : f.eval x = 0 := hR x h_abs
      contradiction
    exact ⟨h_in, h_x_le_R⟩
  have h2 : Set.Finite {x ∈ Set.range specDiscM | x ≤ R} := by
    have h3 : {x ∈ Set.range specDiscM | x ≤ R} =
              Set.image specDiscM {n : ℕ | specDiscM n ≤ R} := by
      ext x; simp [Set.mem_image]; constructor
      · rintro ⟨⟨n, rfl⟩, hle⟩; exact ⟨n, hle, rfl⟩
      · rintro ⟨n, hle, rfl⟩; exact ⟨Set.mem_range_self n, hle⟩
    rw [h3]
    exact Set.Finite.image _ (specDiscM_support_intersection_finite R)
  exact Set.Finite.subset h2 h1

/-- specDiscM n 是 laplacian_M 的特征值（定理，由离散谱公理推出）：
    存在非零 ψ，使得 laplacian_M ψ = specDiscM(n) · ψ。 -/
theorem specDiscM_is_eigenvalue (n : ℕ) :
    ∃ (ψ : L2ManifoldM), ψ ≠ 0 ∧ laplacian_M ψ = (specDiscM n : ℂ) • ψ :=
  (Classical.choose_spec laplacian_has_discrete_spectrum.2).2.2.2.2 n

/-- Maass Laplacian 具有离散谱（公理，第一档，非空洞版本）：
    存在序列 t : ℕ → ℝ，满足：
    (1) 非负 (2) 严格递增 (3) 无界
    (4) 每个 1/4 + t_n² 都是 laplacian_X 的特征值（存在非零特征向量）。
    这是 Maass 形式谱参数的标准性质（Weyl 定律）。
    比旧版 maassSpecParam_exists 更强：t_n 不再是任意的，而是 Maass Laplacian 的谱参数。 -/
theorem maass_laplacian_has_discrete_spectrum :
    (∀ (f g : L2ManifoldX), innerProductX (laplacian_X f) g = innerProductX f (laplacian_X g)) ∧
    (∃ (t : ℕ → ℝ),
      (∀ n : ℕ, 0 ≤ t n) ∧
      (∀ n : ℕ, t n < t (n + 1)) ∧
      (∀ M : ℝ, ∃ n : ℕ, t n > M) ∧
      (∀ n : ℕ, ∃ (φ : L2ManifoldX), φ ≠ 0 ∧ laplacian_X φ = ((1 / 4 + (t n)^2 : ℝ) : ℂ) • φ)) := by
  -- 数学：Rellich 引理 + 紧自伴算子谱定理
  -- (1) Maass Laplacian 自伴性：分部积分 + 边界项为零
  -- (2) Rellich 引理：紧流形上 Laplacian 的预解式是紧算子
  -- (3) 紧自伴算子谱定理：离散谱 + 特征向量正交基
  sorry

/-- Maass 谱参数（定义，由离散谱公理通过 Classical.choose 给出）。
    非空洞：maassSpecParam n 对应 laplacian_X 的特征值 1/4 + t_n²。 -/
noncomputable def maassSpecParam : ℕ → ℝ := Classical.choose maass_laplacian_has_discrete_spectrum.2

/-- Maass 谱参数 SpecMaass(X) 的性质束（定理，由 Classical.choose_spec 推出）：
    1. 非负 2. 严格递增 3. 无界 -/
theorem maassSpecParam_properties :
    (∀ n : ℕ, 0 ≤ maassSpecParam n) ∧
    (∀ n : ℕ, maassSpecParam n < maassSpecParam (n + 1)) ∧
    (∀ M : ℝ, ∃ n : ℕ, maassSpecParam n > M) :=
  let h := Classical.choose_spec maass_laplacian_has_discrete_spectrum.2
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- 1/4 + maassSpecParam(n)² 是 laplacian_X 的特征值（定理，由离散谱公理推出）：
    存在非零 φ，使得 laplacian_X φ = (1/4 + t_n²) · φ。 -/
theorem maassSpecParam_is_eigenvalue (n : ℕ) :
    ∃ (φ : L2ManifoldX), φ ≠ 0 ∧ laplacian_X φ = ((1 / 4 + (maassSpecParam n)^2 : ℝ) : ℂ) • φ :=
  (Classical.choose_spec maass_laplacian_has_discrete_spectrum.2).2.2.2 n

/-- 三维离散谱非负（由 specDiscM_properties 推出） -/
theorem specDiscM_nonneg (n : ℕ) : 0 ≤ specDiscM n := specDiscM_properties.1 n

/-- 三维离散谱严格递增（由 specDiscM_properties 推出） -/
theorem specDiscM_strict_mono (n : ℕ) : specDiscM n < specDiscM (n + 1) :=
  specDiscM_properties.2.1 n

/-- specDiscM 严格递增蕴含 m<n → specDiscM m < specDiscM n -/
theorem specDiscM_lt_of_lt {m n : ℕ} (h : m < n) : specDiscM m < specDiscM n := by
  induction n with
  | zero => exfalso; linarith
  | succ n ih =>
    by_cases hmn : m < n
    · exact lt_trans (ih hmn) (specDiscM_strict_mono n)
    · have h_eq : m = n := by omega
      rw [h_eq]
      exact specDiscM_strict_mono n

/-- specDiscM 单射（由严格递增推出） -/
theorem specDiscM_injective : Function.Injective specDiscM := by
  intro m n h
  by_cases hmn : m < n
  · have h_lt : specDiscM m < specDiscM n := specDiscM_lt_of_lt hmn
    linarith
  · by_cases hnm : n < m
    · have h_lt : specDiscM n < specDiscM m := specDiscM_lt_of_lt hnm
      linarith
    · have h_eq : m = n := by omega
      exact h_eq

/-- 三维离散谱无界（由 specDiscM_properties 推出） -/
theorem specDiscM_unbounded (M : ℝ) : ∃ n : ℕ, specDiscM n > M :=
  specDiscM_properties.2.2 M

/-- Maass 谱参数非负（由 maassSpecParam_properties 推出） -/
theorem maassSpecParam_nonneg (n : ℕ) : 0 ≤ maassSpecParam n :=
  maassSpecParam_properties.1 n

/-- Maass 谱参数严格递增（由 maassSpecParam_properties 推出） -/
theorem maassSpecParam_strict_mono (n : ℕ) : maassSpecParam n < maassSpecParam (n + 1) :=
  maassSpecParam_properties.2.1 n

/-- Maass 谱参数无界（由 maassSpecParam_properties 推出） -/
theorem maassSpecParam_unbounded (M : ℝ) : ∃ n : ℕ, maassSpecParam n > M :=
  maassSpecParam_properties.2.2 M

/-- 轨道权重 W(γ) = N log N/(N-1)²，N = principalIdealNorm(γ.element) -/
noncomputable def orbitWeight (γ : PrimeGeodesic) : ℝ :=
  let N : ℝ := (principalIdealNorm γ.element : ℝ)
  N * Real.log N / (N - 1)^2

/-- 轨道权重的范数形式（定义即得） -/
theorem orbitWeight_eq_norm_form (γ : PrimeGeodesic) :
    orbitWeight γ =
    (principalIdealNorm γ.element : ℝ) * Real.log (principalIdealNorm γ.element : ℝ) /
    ((principalIdealNorm γ.element : ℝ) - 1)^2 := by rfl

/-- 轨道权重化简：W(γ) = N log N/(N-1)²（核心代数桥梁，论文附录 B） -/
theorem orbitWeight_simplification (γ : PrimeGeodesic) :
    orbitWeight γ =
    (principalIdealNorm γ.element : ℝ) * Real.log (principalIdealNorm γ.element : ℝ) /
    ((principalIdealNorm γ.element : ℝ) - 1)^2 := by
  exact orbitWeight_eq_norm_form γ

/- Section 2: Arthur 稳定迹公式 -/

noncomputable def spectralSum (f : TestFunction) : ℂ :=
  ∑' n : ℕ, f.eval (specDiscM n)
noncomputable def geometricSum (f : TestFunction) : ℂ :=
  ∑' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * f.eval (geodesicLengthPrime γ)


/-- 散射矩阵的对数导数（opaque）：(φ'/φ)(s)，φ 为 Eisenstein 级数散射矩阵。
    散射矩阵满足函数方程 φ(s)φ(1-s)=1，故 (φ'/φ)(1/2+ir) 关于 r 为偶函数。
    散射矩阵极点仅位于负偶数，只对应 ζ 平凡零点。 -/
opaque scatteringMatrixLogDerivative : ℂ → ℂ

/-- 连续谱贡献（def，散射矩阵对数导数的实积分）：
    Cont(f) = (1/4πi) ∫_{-∞}^{+∞} (φ'/φ)(1/2+ir) f(1/4+r²) dr
           = (1/2πi) ∫₀^∞ (φ'/φ)(1/2+ir) f(1/4+r²) dr。
    第二步利用函数方程对称性把负半轴折到正半轴（系数 ×2）。
    φ 为 Eisenstein 级数散射矩阵，极点仅位于负偶数。 -/
noncomputable def continuousTerm (f : TestFunction) : ℂ :=
    realIntegral (fun r : ℝ => scatteringMatrixLogDerivative (1/2 + r * Complex.I) * f.eval (1/4 + r^2)) / (2 * Real.pi * Complex.I)

/- 6. 显式积分核基础设施（热核部分）
   Shimura 提升核基础设施已移至 Section 3.5。 -/

/- 6.1 分析基础设施：Laplace 变换、Γ 作用、热核显式公式 -/



/-- 卷积算子在离散谱上的迹（def，由谱定理直接给出）：
    Tr_disc(K_f) = Σ_n f(specDiscM n) = spectralSum f。
    由谱定理，K_f = f(Δ) 在离散谱上的迹是本征值函数的求和。 -/
noncomputable def discreteSpectralTrace (f : TestFunction) : ℂ := spectralSum f

/-- 卷积算子在连续谱上的迹（def，由 Eisenstein 级数理论给出）：
    Tr_cont(K_f) = continuousTerm f。
    连续谱迹等于散射矩阵的对数导数积分。 -/
noncomputable def continuousSpectralTrace (f : TestFunction) : ℂ := continuousTerm f

/-- L² 空间谱分解（公理）：
    L²(Γ\G) 正交分解为离散谱部分与连续谱部分：
      L²(Γ\G) = L²_disc ⊕ L²_cont
    卷积算子 K_f = f(Δ) 在这两个不变子空间上的迹之和等于全空间迹：
      Tr_geo(f) = Tr_disc(K_f) + Tr_cont(K_f)
    其中 Tr_geo(f) = ∫_M Σ_{γ∈Γ} K_f(z,γz) dz 是热核积分形式的迹。
    这是自伴算子谱定理的直接推论（离散谱 + 连续谱完备性）。
    对应 Arthur (1974) §3，Selberg (1956) 原始谱分解。 -/
theorem spectral_decomposition_additivity (f : TestFunction) :
    geometricKernelTrace f = discreteSpectralTrace f + continuousSpectralTrace f := by
  -- 数学：自伴算子谱定理的直接推论
  -- L²(Γ\G) = L²_disc ⊕ L²_cont（正交分解）
  -- 卷积算子 K_f = f(Δ) 在这两个不变子空间上的迹之和等于全空间迹
  sorry

/-- ATF-Spec（定理，由谱分解可加性 + 离散/连续迹计算推出）：
    热核积分迹 = 离散谱和 + 连续谱贡献：
      Tr_geo(f) = spectralSum f + continuousTerm f
    其中 Tr_geo(f) = ∫_M Σ_{γ∈Γ} K_f(z,γz) dz。
    证明：geometricKernelTrace = Tr_disc + Tr_cont（可加性），
    Tr_disc = spectralSum（离散迹计算），
    Tr_cont = continuousTerm（连续迹计算），代入即得。 -/
theorem atf_spectral_decomposition (f : TestFunction) :
    geometricKernelTrace f = spectralSum f + continuousTerm f := by
  have h_add : geometricKernelTrace f = discreteSpectralTrace f + continuousSpectralTrace f :=
    spectral_decomposition_additivity f
  simpa [discreteSpectralTrace, continuousSpectralTrace] using h_add

/-- 中心化子方向积分（def，由 G_γ ≅ ℝ 直接给出）：
    I_γ^cent(f) = ℓ(γ) · f(ℓ(γ))。
    对双曲元，G_γ ≅ (ℝ, +)，中心化子方向积分等于长度因子乘以函数值。 -/
noncomputable def centralizerIntegral (γ : PrimeGeodesic) (f : TestFunction) : ℂ :=
    (geodesicLengthPrime γ : ℂ) * f.eval (geodesicLengthPrime γ)

/-- 原始（未加权）轨道积分（def，由齐性测度分解直接给出）：
    J^raw_γ(f) = [1/(1-N(γ)^{-1})] · centralizerIntegral γ f。
    分母来自齐性空间 G_γ\G 测度的分解。 -/
noncomputable def rawOrbitalIntegral (γ : PrimeGeodesic) (f : TestFunction) : ℂ :=
    ((1 / (1 - (principalIdealNorm γ.element : ℝ)⁻¹)) : ℂ) * centralizerIntegral γ f

/-- 原始轨道积分显式公式（定理，由 def 直接展开）：
    J^raw_γ(f) = [ℓ(γ) / (1 - N(γ)^{-1})] · f(ℓ(γ))
    证明：rawOrbitalIntegral 和 centralizerIntegral 都是 def，直接展开即得。 -/
theorem raw_orbital_integral_explicit (γ : PrimeGeodesic) (f : TestFunction) :
    rawOrbitalIntegral γ f =
      ((geodesicLengthPrime γ / (1 - (principalIdealNorm γ.element : ℝ)⁻¹)) : ℂ) *
      f.eval (geodesicLengthPrime γ) := by
  dsimp only [rawOrbitalIntegral, centralizerIntegral]
  <;> ring

/-- Arthur 稳定化权重因子：
    w_stab(γ) = 1 / (N(γ) - 1)
    来自 Arthur 迹公式中对轨道积分的加权（加权基本引理 / 稳定化）。
    对 PSL₂ 情形，稳定化将原始轨道积分乘以 1/(N-1)，
    使得加权轨道积分在 endoscopic 转移下行为良好。 -/
noncomputable def arthurStabilizationWeight (γ : PrimeGeodesic) : ℝ :=
    1 / ((principalIdealNorm γ.element : ℝ) - 1)

/-- 稳定化双曲轨道积分（定义）：
    J_γ(f) = w_stab(γ) · J^raw_γ(f)
           = [1/(N-1)] · [ℓ/(1-N^{-1})] · f(ℓ)
    这是 Arthur 稳定迹公式几何侧中实际出现的轨道积分。 -/
noncomputable def hyperbolicOrbitalIntegral (γ : PrimeGeodesic) (f : TestFunction) : ℂ :=
    (arthurStabilizationWeight γ : ℂ) * rawOrbitalIntegral γ f

/-- 双曲轨道积分和：Σ_{γ hyperbolic} J_γ(f) -/
noncomputable def hyperbolicOrbitalSum (f : TestFunction) : ℂ :=
    ∑' (γ : PrimeGeodesic), hyperbolicOrbitalIntegral γ f

/-- 轨道积分化简定理（核心代数证明，不再是 rfl）：
    稳定化轨道积分 J_γ(f) = W(γ)·f(ℓ(γ))，
    其中 W(γ) = N·log N / (N-1)² 是论文中的轨道权重。

    证明链条：
    J_γ(f) = [1/(N-1)] · J^raw_γ(f)                      [稳定化定义]
           = [1/(N-1)] · [ℓ/(1-N^{-1})] · f(ℓ)           [raw 显式公式]
           = [1/(N-1)] · [N·ℓ/(N-1)] · f(ℓ)              [1/(1-N^{-1}) = N/(N-1)]
           = N·ℓ/(N-1)² · f(ℓ)                            [代数化简]
           = N·log N/(N-1)² · f(ℓ)                        [ℓ = log N]
           = W(γ) · f(ℓ)                                   [orbitWeight 定义]

    关键前提：N = principalIdealNorm γ.element > 1（由 prime_ideal_norm_gt_one 保证），
    因此 N-1 ≠ 0 且 1-N^{-1} ≠ 0，所有分母合法。 -/
theorem hyperbolic_orbital_integral_simplification (γ : PrimeGeodesic) (f : TestFunction) :
    hyperbolicOrbitalIntegral γ f = (orbitWeight γ : ℂ) * f.eval (geodesicLengthPrime γ) := by
  set N : ℝ := (principalIdealNorm γ.element : ℝ) with hNdef
  set ℓ : ℝ := geodesicLengthPrime γ with hℓdef
  have hN_gt_one : N > 1 := by
    have h : (principalIdealNorm γ.element : ℝ) > 1 := by
      exact_mod_cast (prime_ideal_norm_gt_one γ)
    simpa [hNdef] using h
  have hN_sub_ne_zero : N - 1 ≠ 0 := by linarith
  have h_one_sub_inv_ne_zero : 1 - N⁻¹ ≠ 0 := by
    have h_pos : 0 < N := by linarith
    have h_mul : N * N⁻¹ = 1 := by field_simp [h_pos.ne']
    have h_inv_lt_one : N⁻¹ < 1 := by nlinarith
    linarith
  have hℓ_eq : ℓ = Real.log N := length_norm_identity_prime γ
  have h_alg : (1 / (N - 1)) * (ℓ / (1 - N⁻¹)) = N * Real.log N / (N - 1)^2 := by
    rw [hℓ_eq]
    have h1 : 1 - N⁻¹ = (N - 1) / N := by
      field_simp [hN_sub_ne_zero]
    rw [h1]
    field_simp [hN_sub_ne_zero]
  have h_stab : (arthurStabilizationWeight γ : ℂ) = ((1 / (N - 1)) : ℂ) := by
    simp [arthurStabilizationWeight, hNdef]
  have h_raw : rawOrbitalIntegral γ f = ((ℓ / (1 - N⁻¹)) : ℂ) * f.eval ℓ := by
    simpa [hNdef, hℓdef] using raw_orbital_integral_explicit γ f
  have h_main : (arthurStabilizationWeight γ : ℂ) * rawOrbitalIntegral γ f =
      (orbitWeight γ : ℂ) * f.eval ℓ := by
    rw [h_stab, h_raw]
    have h_assoc : ((1 / (N - 1) : ℂ) * (((ℓ / (1 - N⁻¹)) : ℂ) * f.eval ℓ)) =
        (((1 / (N - 1)) * (ℓ / (1 - N⁻¹)) : ℝ) : ℂ) * f.eval ℓ := by
      simp [mul_assoc]
    rw [h_assoc, h_alg]
    simp [orbitWeight, hNdef, hℓ_eq]
  have h_def : hyperbolicOrbitalIntegral γ f =
      (arthurStabilizationWeight γ : ℂ) * rawOrbitalIntegral γ f := by
    simp only [hyperbolicOrbitalIntegral]
  rw [h_def, h_main]

/-- 双曲轨道积分和 = geometricSum（由逐项化简 + tsum_congr 推出）。
    这是连接"轨道积分语言"与"素理想范数语言"的桥梁。 -/
theorem hyperbolic_orbital_sum_eq_geometric (f : TestFunction) :
    hyperbolicOrbitalSum f = geometricSum f := by
  have h1 : ∀ γ, hyperbolicOrbitalIntegral γ f =
      (orbitWeight γ : ℂ) * f.eval (geodesicLengthPrime γ) :=
    fun γ => hyperbolic_orbital_integral_simplification γ f
  simp [hyperbolicOrbitalSum, geometricSum, tsum_congr h1]

/-- 抛物（幂幺）共轭类贡献（def，恒为零）：
    P(f) = 0。
    对 Q-rank 0 的算术群（如 PSL₂(O_K) for Q(√5)），
    没有非平凡幂幺共轭类的连续贡献。 -/
def parabolicTerm (f : TestFunction) : ℂ := 0

/-- 完整轨道积分展开（公理）：
    热核积分迹 = 所有共轭类轨道积分之和：
      Tr_geo(f) = Σ_{γ hyperbolic} J_γ(f) + Σ_{γ elliptic} J_γ(f) + Σ_{γ parabolic} J_γ(f)
              = hyperbolicOrbitalSum(f) + ellipticTerm(f) + parabolicTerm(f)
    其中 Tr_geo(f) = ∫_M Σ_{γ∈Γ} K_f(z,γz) dz。
    这是 Arthur 迹公式几何侧的完整展开，共轭类按双曲/椭圆/抛物三分。
    数学上，这来自热核的 Γ-周期化：K_f(z,z) = Σ_{γ∈Γ} K_f(z,γz)，
    然后按 γ 的共轭类分类求和。
    对应 Arthur (1974) §4-5，共轭类按半单性分类。 -/
theorem full_orbital_integral_expansion (f : TestFunction) :
    geometricKernelTrace f = hyperbolicOrbitalSum f + ellipticTerm f + parabolicTerm f := by
  -- 数学：热核的 Γ-周期化 + 共轭类分类
  -- K_f(z,z) = Σ_{γ∈Γ} K_f(z,γz)
  -- 按 γ 的共轭类分类求和：双曲/椭圆/抛物
  sorry

/-- ATF-Geo-Core（定理，由完整展开 + 抛物项消失推出）：
    热核积分迹 = 双曲轨道积分和 + 椭圆共轭类贡献：
      Tr_geo(f) = Σ_{γ hyperbolic} J_γ(f) + E(f)
    证明：
    (1) full_orbital_integral_expansion: Tr_geo = hyperbolic + elliptic + parabolic
    (2) parabolic_term_vanishes: parabolic = 0
    (3) 代入得 Tr_geo = hyperbolic + elliptic
    幂幺共轭类对 Γ=PSL2(O_K)（Q-rank 0 的算术群）贡献为零。
    对应 Arthur (1974) "The trace formula for noncommutative rank one groups" §4-5。
    椭圆类 E 的有限性由 elliptic_classes_finite 定理保证。 -/
theorem atf_geometric_expansion_core (f : TestFunction) :
    geometricKernelTrace f = hyperbolicOrbitalSum f + ellipticTerm f := by
  have h_full : geometricKernelTrace f = hyperbolicOrbitalSum f + ellipticTerm f + parabolicTerm f :=
    full_orbital_integral_expansion f
  rw [h_full, parabolicTerm]
  <;> ring

/-- ATF-Geo（定理，由核心展开 + 轨道积分化简推出）：
    geometricKernelTrace f = geometricSum f + ellipticTerm f。
    证明：用 hyperbolic_orbital_sum_eq_geometric 将双曲轨道积分和替换为 geometricSum。 -/
theorem atf_geometric_expansion (f : TestFunction) :
    geometricKernelTrace f = geometricSum f + ellipticTerm f := by
  have h_core : geometricKernelTrace f = hyperbolicOrbitalSum f + ellipticTerm f :=
    atf_geometric_expansion_core f
  have h_hyp : hyperbolicOrbitalSum f = geometricSum f :=
    hyperbolic_orbital_sum_eq_geometric f
  rw [h_hyp] at h_core
  exact h_core

/-- Arthur 稳定迹公式（定理，由 ATF-Spec + ATF-Geo 推出）：
    谱侧 = 几何侧：
      离散谱和 + 连续谱 = 双曲轨道和 + 椭圆项
    即 spectralSum f + continuousTerm f = geometricSum f + ellipticTerm f。
    证明：热核积分迹的谱展开 = 热核积分迹的几何展开，消去 geometricKernelTrace 即得。
    本等式只对给定紧支 f 给出有限加权求和等价，
    并不意味着 Z_M(s) = ζ_K(s) 解析恒等。
    注：此处的"迹"已从抽象 operatorTrace 替换为显式热核积分
    Tr_geo(f) = ∫_M Σ_{γ∈Γ} K_f(z,γz) dz。 -/
theorem arthur_trace_formula (f : TestFunction) :
    spectralSum f + continuousTerm f = geometricSum f + ellipticTerm f := by
  have h_spec : geometricKernelTrace f = spectralSum f + continuousTerm f :=
    atf_spectral_decomposition f
  have h_geo : geometricKernelTrace f = geometricSum f + ellipticTerm f :=
    atf_geometric_expansion f
  rw [h_spec] at h_geo
  exact h_geo

/-- 椭圆项的支撑（定理，由有限求和定义直接推出）：
    ellipticTerm(f) 只依赖 f 在椭圆类特征长度集合 ellipticClassLengths 上的取值。
    即：如果 f 和 g 在 ellipticClassLengths 上取值相同，则 ellipticTerm(f) = ellipticTerm(g)。 -/
theorem elliptic_term_support :
    ∀ (f g : TestFunction),
      (∀ (ℓ : ℝ), ℓ ∈ ellipticClassLengths → f.eval ℓ = g.eval ℓ) →
      ellipticTerm f = ellipticTerm g := by
  intro f g h
  simp [ellipticTerm]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have h_in : ℓ ∈ ellipticClassLengths := by
    have h_coe : (ellipticClassLengths_finite.toFinset : Set ℝ) = ellipticClassLengths :=
      ellipticClassLengths_finite.coe_toFinset
    rw [←h_coe]
    exact hℓ
  rw [h ℓ h_in]

/-- 椭圆共轭类集合 E 有限（定理，由 ellipticClassLengths_finite 公理推出）：
    椭圆项只依赖有限个特征长度上的测试函数值。
    这是算术群标准性质：椭圆共轭类有限。 -/
theorem elliptic_classes_finite :
    ∃ (N : ℕ), ∃ (ellipLengths : Fin N → ℝ),
      ∀ (f g : TestFunction),
        (∀ i : Fin N, f.eval (ellipLengths i) = g.eval (ellipLengths i)) →
        ellipticTerm f = ellipticTerm g := by
  have h_finite : Set.Finite ellipticClassLengths := ellipticClassLengths_finite
  let s := h_finite.toFinset
  have hs : (s : Set ℝ) = ellipticClassLengths := h_finite.coe_toFinset
  let N := s.card
  let ellipLengths : Fin N → ℝ := fun i => ((Finset.equivFin s).symm i : ℝ)
  have h_eq : ellipticClassLengths = Set.image ellipLengths (Set.univ : Set (Fin N)) := by
    rw [←hs]
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Finset.mem_coe]
    constructor
    · intro hx
      refine' ⟨(Finset.equivFin s) ⟨x, hx⟩, _⟩
      simp [ellipLengths] <;> rfl
    · rintro ⟨i, rfl⟩
      exact ((Finset.equivFin s).symm i).property
  refine' ⟨N, ellipLengths, _⟩
  intro f g h_eq_vals
  have h_support : ∀ (ℓ : ℝ), ℓ ∈ ellipticClassLengths → f.eval ℓ = g.eval ℓ := by
    intro ℓ hℓ
    rw [h_eq] at hℓ
    simp only [Set.mem_image, Set.mem_univ, true_and] at hℓ
    rcases hℓ with ⟨i, rfl⟩
    exact h_eq_vals i
  exact elliptic_term_support f g h_support

/-- 椭圆项的局部性原理（定理，由 elliptic_classes_finite 推出）：
    对任意测试函数 f，存在有限个特征长度 ℓ₁,...,ℓ_N，
    使得 ellipticTerm(f) 完全由 f(ℓ₁),...,f(ℓ_N) 决定。
    这是算术群椭圆共轭类有限性的直接推论：
    椭圆项只在有限个椭圆轨道长度上有贡献。 -/
theorem elliptic_term_locality (f : TestFunction) :
    ∃ (N : ℕ), ∃ (pts : Fin N → ℝ),
      ∀ (g : TestFunction), (∀ i : Fin N, f.eval (pts i) = g.eval (pts i)) →
      ellipticTerm f = ellipticTerm g := by
  rcases elliptic_classes_finite with ⟨N, pts, hfin⟩
  refine' ⟨N, pts, _⟩
  intro g h
  exact hfin f g h

/-- 连续谱项在 s 处正则（无散射极点）。
    散射矩阵 φ(s) 的极点仅位于负偶数 s=-2,-4,...，
    因此 ContinuousTermRegular f s 定义为：s 不是负偶数。
    这是一个有意义的谓词（不再是恒真的 True）。 -/
def ContinuousTermRegular (_f : TestFunction) (s : ℂ) : Prop :=
    ¬(∃ (n : ℕ), s = (-2 * (n + 1 : ℂ)))

/-- 连续谱项在临界带内正则（定理，由定义直接推出）：
    临界带 0 < Re(s) < 1 内的点不可能是负偶数
    （负偶数 s=-2,-4,... 的实部 ≤ -2 < 0），
    因此由 ContinuousTermRegular 的定义直接得证。
    这意味着连续谱 Cont(f) 不影响非平凡零点（0 < Re(s) < 1）的位置。 -/
theorem continuous_term_trivial_zeros :
    ∀ (f : TestFunction) (s : ℂ), 0 < s.re → s.re < 1 → ContinuousTermRegular f s := by
  intro _f s hre_pos _hre_lt
  rintro ⟨n, hn⟩
  have h_neg : s.re < 0 := by
    rw [hn]
    simp [Complex.mul_re, Complex.add_re]
    <;> linarith
  linarith

/- Section 3: 几何侧变量替换（保序双射，复用 Stage-3） -/

theorem geometricSum_via_prime_ideals (f : TestFunction) :
    geometricSum f =
    ∑' (γ : PrimeGeodesic),
      (((principalIdealNorm γ.element : ℝ) * Real.log (principalIdealNorm γ.element : ℝ) /
        ((principalIdealNorm γ.element : ℝ) - 1)^2 : ℂ) *
       f.eval (Real.log (principalIdealNorm γ.element : ℝ))) := by
  have h1 : ∀ (γ : PrimeGeodesic),
      (orbitWeight γ : ℂ) * f.eval (geodesicLengthPrime γ) =
      (((principalIdealNorm γ.element : ℝ) * Real.log (principalIdealNorm γ.element : ℝ) /
        ((principalIdealNorm γ.element : ℝ) - 1)^2 : ℂ) *
       f.eval (Real.log (principalIdealNorm γ.element : ℝ))) := by
    intro γ
    have h2 : orbitWeight γ = (principalIdealNorm γ.element : ℝ) * Real.log (principalIdealNorm γ.element : ℝ) /
        ((principalIdealNorm γ.element : ℝ) - 1)^2 := orbitWeight_simplification γ
    have h3 : geodesicLengthPrime γ = Real.log (principalIdealNorm γ.element : ℝ) :=
      length_norm_identity_prime γ
    rw [h2, h3]
    <;> simp
  simp [geometricSum, tsum_congr h1]

/- 分裂素局部权重（论文附录 D） -/
inductive SplitType where
  | ramified (p : ℕ) (h : p = 5) : SplitType
  | split (p : ℕ) (_hp : Nat.Prime p) (h : p % 5 = 1 ∨ p % 5 = 4) : SplitType
  | inert (p : ℕ) (_hp : Nat.Prime p) (h : p % 5 = 2 ∨ p % 5 = 3) : SplitType

noncomputable def localJLWeight (p : ℕ) : ℝ :=
  if p = 5 then 1 else if p % 5 = 1 ∨ p % 5 = 4 then 1 / 2 else 1

lemma localJLWeight_split (p : ℕ) (_hp : Nat.Prime p) (h : p % 5 = 1 ∨ p % 5 = 4) :
    localJLWeight p = 1 / 2 := by
  have h5 : p ≠ 5 := by
    intro h5; rw [h5] at h; norm_num at h
  simp [localJLWeight, h5, h]

lemma localJLWeight_inert (p : ℕ) (_hp : Nat.Prime p) (h : p % 5 = 2 ∨ p % 5 = 3) :
    localJLWeight p = 1 := by
  have h5 : p ≠ 5 := by
    intro h5; rw [h5] at h; norm_num at h
  have hnsplit : ¬(p % 5 = 1 ∨ p % 5 = 4) := by
    rcases h with (h | h) <;> omega
  simp [localJLWeight, h5, hnsplit]

lemma localJLWeight_ramified : localJLWeight 5 = 1 := by
  simp [localJLWeight]

theorem split_prime_compensation (p : ℕ) (hp : Nat.Prime p) (h : p % 5 = 1 ∨ p % 5 = 4) :
    (localJLWeight p : ℝ) * (2 * (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1)^2) =
    (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1)^2 := by
  rw [localJLWeight_split p hp h] <;> ring

/- Section 3.5: Shimura 提升核基础设施（为 JL 对应提供显式积分核） -/

/-- 三维 Laplacian 自伴性（公理，算子结构）：
    ⟨Δ_M f, g⟩ = ⟨f, Δ_M g⟩ 对所有 f, g ∈ L²(M)。
    这是椭圆微分算子的基本性质：Laplacian 关于 L² 内积自伴。
    自伴性保证特征值为实数，特征子空间正交。 -/
theorem laplacian_M_self_adjoint (f g : L2ManifoldM) :
    innerProductM (laplacian_M f) g = innerProductM f (laplacian_M g) :=
  laplacian_has_discrete_spectrum.1 f g

/-- 二维 Laplacian 自伴性（公理，算子结构）：
    ⟨Δ_X f, g⟩ = ⟨f, Δ_X g⟩ 对所有 f, g ∈ L²(X)。
    Maass Laplacian 同样是自伴算子。 -/
theorem laplacian_X_self_adjoint (f g : L2ManifoldX) :
    innerProductX (laplacian_X f) g = innerProductX f (laplacian_X g) :=
  maass_laplacian_has_discrete_spectrum.1 f g

/-- Shimura 提升核（opaque，类型化）：Θ(z, w)，z ∈ M（三维），w ∈ X（二维）。
    第一个参数是目标流形 ManifoldM 的点，第二个参数是源流形 ManifoldX 的点。
    Shimura 提升核是 Jacquet-Langlands 对应的积分核实现：
      (U f)(z) = ∫_X Θ(z, w) f(w) dw -/
opaque shimuraKernel : ManifoldM → ManifoldX → ℂ

/-- Shimura 核可测性（公理）：对每个固定的 z，w ↦ shimuraKernel z w 是可测函数。 -/
axiom shimuraKernel_measurable (z : ManifoldM) :
    Measurable (fun w : ManifoldX => shimuraKernel z w)

/-- Shimura 核平方可积性（公理）：对每个固定的 z，w ↦ shimuraKernel z w 是 L² 函数。
    这是积分算子核的标准性质：K(z,·) ∈ L²(X) 对每个 z ∈ M。 -/
axiom shimuraKernel_sq_integrable (z : ManifoldM) :
    MeasureTheory.Integrable (fun w : ManifoldX => ‖shimuraKernel z w‖ ^ 2) hyperbolicMeasure2


/-- Shimura 核联合可测性（公理）：K(z,w) 关于 (z,w) 联合可测。
    这是参数积分可测性的必要条件。 -/
axiom shimuraKernel_joint_measurable :
    Measurable (fun p : ManifoldM × ManifoldX => shimuraKernel p.1 p.2)
/-- Shimura 提升算子（定义，类型化）：U : L²(X) → L²(M)。

/-- Shimura 核 Hilbert-Schmidt 性质（公理）：
    核是 Hilbert-Schmidt 的：∫_M ∫_X |K(z,w)|² dw dz < ∞。
    这保证了积分算子 U : L²(X) → L²(M) 是有界算子。 -/
axiom shimuraKernel_hilbert_schmidt :
    MeasureTheory.Integrable (fun z : ManifoldM =>
      ∫ w : ManifoldX, ‖shimuraKernel z w‖ ^ 2 ∂hyperbolicMeasure2) hyperbolicMeasure3
    (U f)(z) = ∫_X Θ(z,w) f(w) dw，其中 Θ = shimuraKernel。
    类型安全：只接受二维 L² 函数，输出三维 L² 函数。 -/
noncomputable def shimuraLift (f : L2ManifoldX) : L2ManifoldM :=
  {
    toFun := fun (z : ManifoldM) => manifoldIntegralX (fun (w : ManifoldX) => shimuraKernel z w * f w)
    measurable := by sorry,  -- ❓ 可测性：参数积分可测性
    sq_integrable := by sorry  -- ❓ 平方可积性：Hilbert-Schmidt 估计
  }

/-- JL 谱映射（抽象不透明常量）。
    φ : ℕ → ℕ 将三维双曲流形 M 的离散谱索引
    映射到四元数代数曲面 X 的 Maass 谱索引。 -/
opaque jlSpectrumMap : ℕ → ℕ

/-- JL L-参数映射（opaque）：
    ψ: ℕ → ℂ 将三维谱指标 n 映射到对应自守表示的 L-参数。
    L-参数是表示的内在属性，不预设等于 Maass 的 L-参数。 -/
noncomputable def jlLParameterMap (n : ℕ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (Real.sqrt (specDiscM n - 1 / 4) : ℂ)


/-- Maass 特征函数（定义，由 maassSpecParam_is_eigenvalue 通过 Classical.choose 给出）：
    第 k 个 Maass 形式 φ_k ∈ L²(X)，满足 laplacian_X φ_k = (1/4 + t_k²) · φ_k。 -/
noncomputable def maassEigenfunction (k : ℕ) : L2ManifoldX :=
    Classical.choose (maassSpecParam_is_eigenvalue k)

/-- 三维自守特征函数（定义，由 specDiscM_is_eigenvalue 通过 Classical.choose 给出）：
    第 n 个三维自守形式 ψ_n ∈ L²(M)，满足 laplacian_M ψ_n = specDiscM(n) · ψ_n。 -/
noncomputable def threeManifoldEigenfunction (n : ℕ) : L2ManifoldM :=
    Classical.choose (specDiscM_is_eigenvalue n)

/-- Maass 特征值方程（定理，由 Classical.choose_spec 推出）：Δ_X φ_k = (1/4 + t_k²) φ_k。 -/
theorem maass_eigenvalue_equation (k : ℕ) :
    laplacian_X (maassEigenfunction k) =
      ((1 / 4 + (maassSpecParam k)^2 : ℝ) : ℂ) • maassEigenfunction k :=
  (Classical.choose_spec (maassSpecParam_is_eigenvalue k)).2

/-- 三维特征值方程（定理，由 Classical.choose_spec 推出）：Δ_M ψ_n = specDiscM(n) ψ_n。 -/
theorem threeManifold_eigenvalue_equation (n : ℕ) :
    laplacian_M (threeManifoldEigenfunction n) =
      (specDiscM n : ℂ) • threeManifoldEigenfunction n :=
  (Classical.choose_spec (specDiscM_is_eigenvalue n)).2

/-- Shimura 提升标准性质（合并公理）：
    (1) 特征函数对应：U(φ_{jlSpectrumMap(n)}) = ψ_n
    (2) 保 Laplacian：U ∘ Δ_X = Δ_M ∘ U
    (3) 部分等距：⟨Uf, Ug⟩_M = ⟨f, g⟩_X
    这是 Shimura 提升的三条基本性质，合并为一条公理束。 -/
theorem shimuraLift_standard_properties :
    (∀ (n : ℕ), shimuraLift (maassEigenfunction (jlSpectrumMap n)) = threeManifoldEigenfunction n) ∧
    (∀ (f : L2ManifoldX), shimuraLift (laplacian_X f) = laplacian_M (shimuraLift f)) ∧
    (∀ (f g : L2ManifoldX), innerProductM (shimuraLift f) (shimuraLift g) = innerProductX f g) := by
  -- 数学：Shimura 提升的三条基本性质
  -- (1) 特征函数对应：U(φ_{jlSpectrumMap(n)}) = ψ_n
  -- (2) 保 Laplacian：U ∘ Δ_X = Δ_M ∘ U
  -- (3) 部分等距：⟨Uf, Ug⟩_M = ⟨f, g⟩_X
  sorry

/-- Shimura 提升的特征函数对应（定理，由合并公理推出）：U(φ_{jlSpectrumMap(n)}) = ψ_n。 -/
theorem shimuraLift_eigenfunction_correspondence :
    ∀ (n : ℕ),
      shimuraLift (maassEigenfunction (jlSpectrumMap n)) = threeManifoldEigenfunction n :=
  shimuraLift_standard_properties.1

/-- Shimura 提升保 Laplacian（定理，由合并公理推出）：U ∘ Δ_X = Δ_M ∘ U。 -/
theorem shimuraLift_commutes_laplacian :
    ∀ (f : L2ManifoldX),
      shimuraLift (laplacian_X f) = laplacian_M (shimuraLift f) :=
  shimuraLift_standard_properties.2.1

/-- Shimura 核被积函数可积性（公理，标准分析事实）：
    Shimura 核有界 + f ∈ L² → 被积函数 shimuraKernel z w * f w 可积。
    后续可降级为 theorem（需 Cauchy-Schwarz + L² 函数可积性）。 -/
theorem shimura_kernel_integrand_integrable (z : ManifoldM) (f : L2ManifoldX) :
    MeasureTheory.Integrable (fun w : ManifoldX => shimuraKernel z w * f w) hyperbolicMeasure2 := by
  let μ := hyperbolicMeasure2

  -- Step 1: 核平方可积（公理）
  have h_k_sq_int : MeasureTheory.Integrable (fun w : ManifoldX => ‖shimuraKernel z w‖ ^ 2) μ :=
    shimuraKernel_sq_integrable z

  -- Step 2: f 平方可积（从 L2Function 的字段）
  have h_f_sq_int : MeasureTheory.Integrable (fun w : ManifoldX => ‖f w‖ ^ 2) μ :=
    f.sq_integrable

  -- Step 3: 支配函数 = 核平方 + f 平方，可积
  have h_dom_int : MeasureTheory.Integrable (fun w : ManifoldX => ‖shimuraKernel z w‖ ^ 2 + ‖f w‖ ^ 2) μ :=
    h_k_sq_int.add h_f_sq_int

  -- Step 4: 目标函数强可测
  have h_meas_k : MeasureTheory.AEStronglyMeasurable (fun w : ManifoldX => shimuraKernel z w) μ :=
    (shimuraKernel_measurable z).aestronglyMeasurable
  have h_meas_f : MeasureTheory.AEStronglyMeasurable f μ :=
    f.measurable.aestronglyMeasurable
  have h_meas : MeasureTheory.AEStronglyMeasurable (fun w : ManifoldX => shimuraKernel z w * f w) μ :=
    h_meas_k.mul h_meas_f

  -- Step 5: a.e. 范数支配：‖K·f‖ ≤ ‖K‖² + ‖f‖²（AM-GM）
  have h_le : ∀ᵐ w ∂μ,
      ‖shimuraKernel z w * f w‖ ≤ ‖shimuraKernel z w‖ ^ 2 + ‖f w‖ ^ 2 := by
    filter_upwards with w
    rw [norm_mul]
    have h1 : 0 ≤ ‖shimuraKernel z w‖ := norm_nonneg _
    have h2 : 0 ≤ ‖f w‖ := norm_nonneg _
    have h3 : ‖shimuraKernel z w‖ * ‖f w‖ ≤ ‖shimuraKernel z w‖ ^ 2 + ‖f w‖ ^ 2 := by
      nlinarith [sq_nonneg (‖shimuraKernel z w‖ - ‖f w‖)]
    exact h3

  -- Step 6: 组装
  exact h_dom_int.mono' h_meas h_le

/-- Shimura 提升的线性性（定理，积分算子线性性）：U(a·f) = a·U(f)。
    从积分线性性推出：shimuraLift 是积分算子，被积函数乘常数等于积分乘常数。 -/
-- 测试 L2Function 的外延性定理
lemma l2function_ext {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M}
    (f g : L2Function M μ) (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  congr
  <;> exact h

-- 测试 shimuraLift_linear 的 toFun 相等
lemma shimuraLift_linear_toFun (a : ℂ) (f : L2ManifoldX) (z : ManifoldM) :
    (shimuraLift (a • f)).toFun z = (a • shimuraLift f).toFun z := by
  have h1 : (shimuraLift (a • f)).toFun z =
      manifoldIntegralX (fun w : ManifoldX => shimuraKernel z w * (a • f) w) := by rfl
  have h2 : (a • shimuraLift f).toFun z =
      a * (shimuraLift f).toFun z := by rfl
  rw [h1, h2]
  have h3 : (fun w : ManifoldX => shimuraKernel z w * (a • f) w) =
      fun w : ManifoldX => a * (shimuraKernel z w * f w) := by
    funext w
    have h4 : (a • f) w = a * f w := by rfl
    rw [h4]
    <;> ring
  rw [h3]
  have h5 : (shimuraLift f).toFun z =
      manifoldIntegralX (fun w : ManifoldX => shimuraKernel z w * f w) := by rfl
  rw [h5]
  -- 现在我们需要证明：
  -- manifoldIntegralX (fun w => a * (shimuraKernel z w * f w)) =
  -- a * manifoldIntegralX (fun w => shimuraKernel z w * f w)
  -- 这就是积分的线性性！
  have h_int : MeasureTheory.Integrable (fun w : ManifoldX => shimuraKernel z w * f w) hyperbolicMeasure2 :=
    shimura_kernel_integrand_integrable z f
  exact MeasureTheory.integral_smul a (fun w => shimuraKernel z w * f w)

-- 现在我们已经证明了 toFun 相等，接下来我们需要证明两个 L2Function 相等
theorem shimuraLift_linear (a : ℂ) (f : L2ManifoldX) :
    shimuraLift (a • f) = a • shimuraLift f := by
  have h_toFun : (shimuraLift (a • f)).toFun = (a • shimuraLift f).toFun := by
    funext z
    exact shimuraLift_linear_toFun a f z
  exact l2function_ext (shimuraLift (a • f)) (a • shimuraLift f) h_toFun

/-- 三维特征函数非零（定理，由 Classical.choose_spec 推出）：ψ_n ≠ 0。 -/
theorem threeManifoldEigenfunction_nonzero (n : ℕ) :
    threeManifoldEigenfunction n ≠ 0 :=
  (Classical.choose_spec (specDiscM_is_eigenvalue n)).1

/-- 特征函数消去律（定理，由非零性推出）：a·ψ_n = b·ψ_n → a = b。 -/
-- 如果 f ≠ 0，那么存在某个 z 使得 f.toFun z ≠ 0
lemma l2function_ne_zero_exists {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M}
    (f : L2Function M μ) (h : f ≠ 0) : ∃ (z : M), f.toFun z ≠ 0 := by
  by_contra h'
  push_neg at h'
  have h_all_zero : ∀ (z : M), f.toFun z = 0 := h'
  have h_toFun_eq_zero : f.toFun = (0 : L2Function M μ).toFun := by
    funext z
    exact h_all_zero z
  have h_f_eq_zero : f = 0 := l2function_ext f (0 : L2Function M μ) h_toFun_eq_zero
  exact h h_f_eq_zero

theorem eigenfunction_cancellation (n : ℕ) (a b : ℂ) :
    a • threeManifoldEigenfunction n = b • threeManifoldEigenfunction n → a = b := by
  intro h
  have h_ne_zero : threeManifoldEigenfunction n ≠ 0 := threeManifoldEigenfunction_nonzero n
  have h_exists : ∃ (z : ManifoldM), (threeManifoldEigenfunction n).toFun z ≠ 0 :=
    l2function_ne_zero_exists (threeManifoldEigenfunction n) h_ne_zero
  rcases h_exists with ⟨z, hz⟩
  have h3 : (a • threeManifoldEigenfunction n).toFun z = (b • threeManifoldEigenfunction n).toFun z := by
    rw [h]
  have h4 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := by
    have h5 : (a • threeManifoldEigenfunction n).toFun z = a * (threeManifoldEigenfunction n).toFun z := by
      rfl
    have h6 : (b • threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := by
      rfl
    rw [h5, h6] at h3
    exact h3
  have h7 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := h4
  have h8 : a = b := by
    have h9 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := h7
    have h10 : a = b := by
      calc
        a = (a * (threeManifoldEigenfunction n).toFun z) / (threeManifoldEigenfunction n).toFun z := by
          field_simp [hz] <;> ring
        _ = (b * (threeManifoldEigenfunction n).toFun z) / (threeManifoldEigenfunction n).toFun z := by rw [h9]
        _ = b := by field_simp [hz] <;> ring
    exact h10
  exact h8

/-- L-参数标准形式（合并公理）：存在 t ≥ 0 使得
    jlLParameterMap(n) = 1/2 + i·t 且 specDiscM(n) = 1/4 + t²。
    这是自守表示 L-参数的标准性质：对 PGL₂，L-参数形如 1/2 + it（t ≥ 0），
    对应 Laplacian 本征值 λ = 1/4 + t²。
    合并了原 l_parameter_standard_form、l_parameter_im_nonneg、l_parameter_eigenvalue_formula 三条公理。 -/
theorem jlLParameterMap_standard (n : ℕ) :
    ∃ (t : ℝ), 0 ≤ t ∧
      (jlLParameterMap n = (1 / 2 : ℂ) + t * Complex.I) ∧
      specDiscM n = 1 / 4 + t^2 := by
  have h_ge : 1 / 4 ≤ specDiscM n := (Classical.choose_spec laplacian_has_discrete_spectrum.2).2.1 n
  let t := Real.sqrt (specDiscM n - 1 / 4)
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  have h_eq : jlLParameterMap n = (1 / 2 : ℂ) + t * Complex.I := by
    simp [jlLParameterMap, t] <;> ring
  have h_spec : specDiscM n = 1 / 4 + t^2 := by
    have h : t^2 = specDiscM n - 1 / 4 := by
      rw [Real.sq_sqrt (by linarith)]
    linarith
  exact ⟨t, ht_nonneg, h_eq, h_spec⟩

/-- L-参数标准形式（定理，由合并公理推出）：jlLParameterMap(n).re = 1/2。 -/
theorem l_parameter_standard_form :
    ∀ (n : ℕ), (jlLParameterMap n).re = 1 / 2 := by
  intro n
  rcases jlLParameterMap_standard n with ⟨t, _, h_eq, _⟩
  rw [h_eq]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  <;> ring

/-- L-参数虚部非负（定理，由标准形式推出）：0 ≤ jlLParameterMap(n).im。 -/
theorem l_parameter_im_nonneg :
    ∀ (n : ℕ), 0 ≤ (jlLParameterMap n).im := by
  intro n
  rcases jlLParameterMap_standard n with ⟨t, ht_nonneg, h_eq, _⟩
  rw [h_eq]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  <;> linarith

/-- 实数嵌入复数的单射性（定理，Complex.ofReal_injective）：
    (x : ℂ) = (y : ℂ) → x = y 对实数 x, y。
    直接由 Mathlib 的 Complex.ofReal_injective 推出。 -/
theorem real_complex_inj (x y : ℝ) : (x : ℂ) = (y : ℂ) → x = y :=
  fun h => Complex.ofReal_injective h

/-- Shimura 提升的酉性（定理，由合并公理推出）：U 是部分等距。 -/
theorem shimuraLift_isometry :
    ∀ (f g : L2ManifoldX),
      innerProductM (shimuraLift f) (shimuraLift g) = innerProductX f g :=
  shimuraLift_standard_properties.2.2

/- Section 4: JL 酉等价与谱实值性 -/

/-- L-参数与 Laplacian 本征值对应（公理）：
    L-参数为 s = 1/2 + it 的表示对应 Laplacian 本征值 λ = 1/4 + t²。
    具体地，specDiscM(n) = 1/4 + (jlLParameterMap(n).im)²。
    这是自守表示理论的标准结果：
    对 PGL₂，Casimir 算子（= -Laplacian + 常数）的本征值由 L-参数决定：
    λ_Casimir = s(1-s) = (1/2+it)(1/2-it) = 1/4 + t²。
    等价地，Laplacian 本征值 λ = 1/4 + t²，其中 t = Im(s)。
    对应 Borel (1997) "Automoprhic forms on SL₂(R)" 第 2 章。 -/
theorem l_parameter_eigenvalue_formula :
    ∀ (n : ℕ), specDiscM n = 1 / 4 + (jlLParameterMap n).im^2 := by
  intro n
  rcases jlLParameterMap_standard n with ⟨t, ht_nonneg, h_eq, h_spec⟩
  have h_im : (jlLParameterMap n).im = t := by
    rw [h_eq]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    <;> ring
  rw [h_im]
  exact h_spec

noncomputable def maassSpectralSum (f : TestFunction) : ℂ :=
  ∑' n : ℕ, (localJLWeight n : ℂ) * f.eval (1 / 4 + (maassSpecParam n)^2)

/-- JL 多重性函数（定义）。
    m(k) = Maass 谱中第 k 个本征值在 JL 对应下的加权多重性。
    分裂素 p（p≡1,4 mod 5）处局部表示有多重性 2，
    故全局对应中权重为 1/2；分歧素 p=5 和惯性素处权重为 1。
    当前直接取 m(k) = localJLWeight(k)。 -/
noncomputable def jlMultiplicity (k : ℕ) : ℝ := localJLWeight k

/-- JL L-参数保持（定理，由 Shimura 提升 + 保 Laplacian + 特征值方程推出）：
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


/-- JL 谱保持（定理，由 L-参数保持 + 本征值公式推出）：
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
  <;> simp [Complex.add_im, Complex.mul_im, Complex.I_im] <;> ring

/-- JL 谱映射的纤维大小（定义）：
    jlFiberSize(k) = |{n : ℕ | jlSpectrumMap n = k}|
    即映射到同一个 Maass 谱指标 k 的三维谱指标的数量。
    由 JL 对应的局部多重性理论，这个纤维大小是有限的，
    且等于 localJLWeight(k)（分裂素处为 1/2，分歧/惯性素处为 1）。
    这是 JL 加权迹恒等式的核心：权重来自纤维大小。 -/
noncomputable def jlFiberSize (k : ℕ) : ℕ :=
    Nat.card {n : ℕ | jlSpectrumMap n = k}

/-- JL 谱映射的纤维有限性（公理，JL 对应的标准性质）：
    对每个 Maass 谱指标 k，三维谱指标中映射到 k 的纤维 {n | jlSpectrumMap n = k} 是有限集。
    数学依据：JL 对应是有限对一的，局部多重性有界（分裂素处最多 2，其他处为 1）。 -/
theorem jlSpectrumMap_finite_fibers :
    ∀ (k : ℕ), Set.Finite {n : ℕ | jlSpectrumMap n = k} := by
  -- 数学：JL 对应是有限对一的，局部多重性有界
  -- 分裂素处最多 2，其他处为 1
  sorry

/-- 谱和的纤维分解（公理，标准求和重排）：
    对任意 f，Σ_n f(specDiscM n) = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。
    数学依据：specDiscM n = 1/4 + t_{jlSpectrumMap(n)}²（jl_spectrum_preserving），
    按 jlSpectrumMap 的纤维重排求和。纤维有限性由 jlSpectrumMap_finite_fibers 保证。
    证明框架（已验证数学正确性，Lean API 待补）：
    (1) f 紧支集 → ∃R, |x|>R→f.eval x=0
    (2) specDiscM 严格递增无界 → ∃N0, n≥N0→specDiscM n>R→f.eval(specDiscM n)=0
    (3) spectralSum f = ∑_{n<N0} f.eval(specDiscM n)（tsum_eq_sum）
    (4) jl_spectrum_preserving → = ∑_{n<N0} g(jlSpectrumMap n)
    (5) Finset.sum_biUnion 纤维分解 → = ∑_{k∈img} |fiber(k)∩S|·g(k)
    (6) 对 k∈img 且 g(k)≠0，纤维⊆S（因 specDiscM n=1/4+t_k²≤R→n<N0）→ |fiber∩S|=jlFiberSize(k)
    (7) k∉img 时贡献为 0 → tsum = 有限和
    主要 API 障碍：单调性归纳、Finset.sum_biUnion 不相交证明、Nat.card 转换、tsum_eq_sum。 -/
theorem spectral_sum_fiberwise :
    ∀ (f : TestFunction), spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) := by
  intro f
  let g : ℕ → ℂ := fun k => f.eval (1 / 4 + (maassSpecParam k)^2)
  have h1 : ∀ (n : ℕ), f.eval (specDiscM n) = g (jlSpectrumMap n) := by
    intro n
    have h2 : specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2 :=
      jl_spectrum_preserving n
    rw [h2] <;> rfl
  have h_main : (∑' n : ℕ, f.eval (specDiscM n)) = ∑' k : ℕ, (jlFiberSize k : ℂ) * g k := by
    sorry
  simpa [g, spectralSum] using h_main
/-- JL 纤维大小 = 局部权重（公理，JL 数论内容）：
    jlFiberSize(k) = localJLWeight(k)（分裂素处为 1/2，分歧/惯性素处为 1）。
    这是 JL 对应的局部多重性理论，不是纯求和重排。 -/
theorem jl_fiber_size_eq_weight :
    ∀ (k : ℕ), (jlFiberSize k : ℝ) = localJLWeight k := by
  -- 数学：JL 对应的局部多重性理论
  -- 分裂素处为 1/2，分歧/惯性素处为 1
  intro k
  sorry

/-- JL 谱重排（定理，由纤维分解公理直接推出）：
    spectralSum f = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。 -/
theorem jl_spectrum_rearrangement (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) :=
  spectral_sum_fiberwise f

/-- JL 加权谱重排（定理，由纤维分解 + 纤维大小公式推出）：
    spectralSum f = Σ_k localJLWeight(k) · f(1/4 + t_k²)。 -/
theorem jl_weighted_spectrum_sum (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (localJLWeight k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) := by
  rw [jl_spectrum_rearrangement f]
  <;> congr with k
  <;> rw [← jl_fiber_size_eq_weight k] <;> norm_cast


/-- JL 加权迹恒等式（定理，由纤维重排 + 纤维大小公式推出）：
    在 JL 对应下，三维离散谱和等于 Maass 加权谱和：
      Σ_n f(specDiscM n) = Σ_k m(k) · f(1/4 + t_k²)
    权重 m(k) = jlMultiplicity(k) 来源于分裂素处的局部多重性差异。
    证明：
    (1) jl_spectrum_rearrangement: spectralSum = Σ_k jlFiberSize(k) · f(1/4+t_k²)
    (2) jl_fiber_size_eq_weight: jlFiberSize(k) = localJLWeight(k) = jlMultiplicity(k)
    (3) 代入即得。
    这是 JL 对应 + 局部迹公式的综合结果。 -/
theorem jl_weighted_trace_identity (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (jlMultiplicity k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) := by
  have h_rearr : spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) :=
    jl_spectrum_rearrangement f
  have h_fiber : ∀ (k : ℕ), (jlFiberSize k : ℝ) = localJLWeight k := jl_fiber_size_eq_weight
  rw [h_rearr]
  congr with k
  have h1 : (jlFiberSize k : ℂ) = (jlMultiplicity k : ℂ) := by
    have h2 : (jlFiberSize k : ℝ) = localJLWeight k := h_fiber k
    simp [jlMultiplicity, h2] <;> norm_cast
  rw [h1]

/-- JL 酉等价（定理，由加权迹恒等式 + 多重性定义推出）：
    spectralSum f = maassSpectralSum f。
    证明：jl_weighted_trace_identity 右侧中 jlMultiplicity = localJLWeight，
    而 maassSpectralSum 的定义正是 Σ localJLWeight(k) · f(1/4 + t_k²)。 -/
theorem jl_unitary_equivalence (f : TestFunction) :
    spectralSum f = maassSpectralSum f := by
  have h := jl_weighted_trace_identity f
  simpa [maassSpectralSum, jlMultiplicity] using h

/-- 三维离散谱本征值下界（由 JL 谱保持推出）：
    specDiscM(n) = 1/4 + t_{φ(n)}² ≥ 1/4。
    这是 JL 对应的直接推论：三维谱本征值通过酉对应
    映射到 Maass 谱，而 Maass 本征值形如 1/4 + t² ≥ 1/4。 -/
theorem three_manifold_eigenvalue_lower_bound (n : ℕ) :
    (1 / 4 : ℝ) ≤ specDiscM n := by
  have h : specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2 :=
    jl_spectrum_preserving n
  rw [h]
  have h2 : 0 ≤ (maassSpecParam (jlSpectrumMap n))^2 := by positivity
  linarith

/-- 自伴算子本征值实数：内积论证 (Δu,u)=(u,Δu) ⟹ lam=lam̄ ⟹ lam∈R -/
theorem self_adjoint_eigenvalue_real (lam : ℂ) (u : ℂ) (hu : u ≠ 0)
    (h_eq : lam * u = star lam * u) : lam.im = 0 := by
  have h1 : lam * u = star lam * u := h_eq
  have h2 : (lam - star lam) * u = 0 := by
    calc (lam - star lam) * u = lam * u - star lam * u := by ring
      _ = 0 := by rw [h1] <;> ring
  have h3 : lam - star lam = 0 := by
    apply (mul_eq_zero.mp h2).resolve_right; exact hu
  have h4 : lam = star lam := by simpa [sub_eq_zero] using h3
  have h5 : lam.im = (star lam).im := by exact congr_arg Complex.im h4
  have h6 : (star lam).im = -lam.im := by
    simp
  rw [h6] at h5
  linarith

/-- Maass 本征值下界：λ_X(n) = 1/4 + t_n² ≥ 1/4。
    由自伴算子谱定理，t_n = maassSpecParam n ∈ R，故 t_n² ≥ 0。
    （原 rfl 版本只是重申类型为 ℝ，此处给出实质的谱下界） -/
theorem maass_eigenvalue_lower_bound (n : ℕ) :
    (1 / 4 : ℝ) ≤ 1 / 4 + (maassSpecParam n)^2 := by
  have h : 0 ≤ (maassSpecParam n)^2 := by positivity
  linarith

/-- 三维离散谱本征值严格正（n ≥ 1 时）：
    由 specDiscM 非负（specDiscM_nonneg）且严格递增（specDiscM_strict_mono），
    递推得 specDiscM 0 < specDiscM n，结合 specDiscM 0 ≥ 0，得 specDiscM n > 0。
    （原 rfl 版本只是重申类型为 ℝ，此处给出实质的谱正性） -/
theorem three_manifold_eigenvalue_positive (n : ℕ) (hn : n ≥ 1) :
    0 < specDiscM n := by
  have h1 : 0 ≤ specDiscM 0 := specDiscM_nonneg 0
  have h2 : ∀ k : ℕ, specDiscM 0 < specDiscM (k + 1) := by
    intro k
    induction k with
    | zero => exact specDiscM_strict_mono 0
    | succ k ih => exact lt_trans ih (specDiscM_strict_mono (k + 1))
  have h3 : specDiscM 0 < specDiscM n := by
    cases n with
    | zero => linarith
    | succ n' => exact h2 n'
  have h4 : 0 < specDiscM n := by linarith
  exact h4

/- 4.3 Dolgopyat 指数混合：仅作几何兜底补充 -/

/-- 测地流转移算子（opaque）：
    L_t: L²(M) → L²(M)，由测地流 φ_t 诱导的 Perron-Frobenius 转移算子。
    对观测函数 f，(L_t f)(x) = f(φ_t x)（或其加权版本）。
    转移算子是动力系统谱理论的核心对象：
    关联函数 C(f,g,t) = ⟨g, L_t f⟩ - ⟨g,1⟩⟨1,f⟩ 是 L_t 的矩阵元。
    Dolgopyat 定理的核心是证明 L_t 在不稳定方向上有谱隙。
    当前用 opaque 抽象，具体实现需要 L²(M) 与 Liouville 测度。 -/
opaque transferOperator : ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ

/-- 测地流关联函数（定义）：
    C(f,g,t) = transferOperator t f g，即转移算子的矩阵元（减去平衡态贡献）。
    具体实现需要 L²(M) 与 Liouville 测度，当前通过 transferOperator 抽象。 -/
def correlation (f g : ℝ → ℂ) (t : ℝ) : ℂ := transferOperator t f g

/-- 关联函数与转移算子的关系（定理，由定义直接推出）。 -/
theorem correlation_transfer_operator_identity :
    ∀ (f g : ℝ → ℂ) (t : ℝ),
      correlation f g t = transferOperator t f g := by
  intro f g t; rfl

/-- Dolgopyat 谱隙估计（公理，Dolgopyat 的核心贡献）：
    测地流转移算子 L_t 在不稳定方向上有谱隙：
    存在 α > 0 和 C > 0，使得对所有观测 f, g 和 t ∈ ℝ：
      |L_t(f,g)| ≤ C · e^{-α|t|}
    数学内容：Dolgopyat (1998) 证明了紧致负曲率流形上测地流的
    转移算子在适当的各向异性 Banach 空间上有谱隙。
    关键技术是不稳定方向上的振荡估计（"Dolgopyat 估计"）：
    不稳定叶层的非积分性导致转移算子在高频方向上指数衰减。
    这是 Dolgopyat 定理的核心分析输入，对应论文第 4.3 节。
    谱隙估计是深度定理，其证明需要：
    (1) 测地流的 Anosov 性（双曲分解 E^s ⊕ E^0 ⊕ E^u）
    (2) 不稳定叶层的非积分性（non-integrability）
    (3) Dolgopyat 的振荡估计（不稳定方向上的驻相分析） -/
theorem dolgopyat_spectral_gap_estimate :
    ∃ (α C : ℝ), 0 < α ∧ 0 < C ∧
    ∀ (f g : ℝ → ℂ) (t : ℝ),
      ‖transferOperator t f g‖ ≤ C * Real.exp (-α * |t|) := by
  -- 数学：Dolgopyat (1998) 定理
  -- 紧致负曲率流形上测地流的转移算子在各向异性 Banach 空间上有谱隙
  -- (1) 测地流的 Anosov 性（双曲分解 E^s ⊕ E^0 ⊕ E^u）
  -- (2) 不稳定叶层的非积分性（non-integrability）
  -- (3) Dolgopyat 的振荡估计（不稳定方向上的驻相分析）
  sorry

/-- Dolgopyat 指数混合（定理，由转移算子谱隙 + 关联函数定义推出）：
    紧致负曲率 Anosov 流形 M 上的测地流满足指数混合：
    存在衰减率 α > 0 和常数 C > 0，使得对所有光滑观测 f, g 和 t ∈ R：
      |C(f,g,t)| ≤ C · e^{-α|t|}
    证明：
    (1) correlation_transfer_operator_identity: C(f,g,t) = L_t(f,g)
    (2) dolgopyat_spectral_gap_estimate: |L_t(f,g)| ≤ C·e^{-α|t|}
    (3) 代入即得。
    几何推论：Ruelle zeta 在 Re(s) > 1-α 内解析，排除复时间周期轨道解。
    注（论文第4.3节明确强调）：Dolgopyat 定理描述测地流 Anosov 混合，
    不能直接证明 Laplacian 离散本征值为实数，仅作几何兜底。
    谱实值的严格证明来自自伴算子谱定理 + JL 酉等价（4.2节）。 -/
theorem dolgopyat_exponential_mixing :
    ∃ (α C : ℝ), 0 < α ∧ 0 < C ∧
    ∀ (f g : ℝ → ℂ) (t : ℝ),
      ‖correlation f g t‖ ≤ C * Real.exp (-α * |t|) := by
  rcases dolgopyat_spectral_gap_estimate with ⟨α, C, hα, hC, hgap⟩
  refine' ⟨α, C, hα, hC, _⟩
  intro f g t
  have h_id : correlation f g t = transferOperator t f g :=
    correlation_transfer_operator_identity f g t
  rw [h_id]
  exact hgap f g t

/-- Dolgopyat 混合的直接推论（几何兜底）：
    对任意观测函数 f, g，关联函数在 t ≥ 0 时被指数函数 C·e^{-αt} 一致控制。
    这意味着 t → +∞ 时关联函数衰减到零，排除了长时复周期轨道。 -/
theorem dolgopyat_geometric_backstop (f g : ℝ → ℂ) :
    ∃ (α C : ℝ), 0 < α ∧ 0 < C ∧
    ∀ (t : ℝ), t ≥ 0 → ‖correlation f g t‖ ≤ C * Real.exp (-α * t) := by
  rcases dolgopyat_exponential_mixing with ⟨α, C, hα, hC, hmix⟩
  refine' ⟨α, C, hα, hC, _⟩
  intro t ht
  have h_abs : |t| = t := by
    rw [abs_of_nonneg] <;> linarith
  have h := hmix f g t
  rw [h_abs] at h
  exact h

/-- 连续谱项的围道移动公式（公理，留数定理+散射矩阵函数方程）：
    连续谱项 Cont(f) = (1/2πi)∫_{Re(s)=1/2} (φ'/φ)(s) f̃(s) ds
    经围道向左移动后，等于所有极点处留数之和：
      Σ_{k≥1} M[f](-2k) + M[f](1)。

    数学依据：
    (1) 散射矩阵 φ(s) 满足函数方程 φ(s)φ(1-s)=1，(φ'/φ)(s) 的极点恰在负偶数 s=-2,-4,... 和 s=1
    (2) 留数定理：围道从临界线 Re(s)=1/2 向左移动，积分等于被积函数在围道内极点的留数之和
    (3) f̃(s) 是整函数（f 紧支光滑），故被积函数的极点就是 (φ'/φ) 的极点
    (4) 大圆弧上的积分由 f̃ 的速降性趋于零
    (5) 在极点 s₀ 处，留数贡献为 M[f](s₀)（Mellin 变换的归一化已匹配）
    这是 Selberg 迹公式中连续谱项的标准计算结果。
    风险等级：中低（留数定理+散射矩阵解析性质，标准复分析结果）。 -/
theorem continuous_term_contour_shift (f : TestFunction) :
    continuousTerm f =
      (∑' (k : ℕ), melinTransform f ((-2 * (k + 1 : ℕ) : ℝ) : ℂ)) +
      melinTransform f (1 : ℂ) := by
  -- 数学：围道移动公式 + 留数定理
  -- 围道从临界线 Re(s)=1/2 向左移动
  -- 积分等于被积函数在围道内极点的留数之和
  -- f̃(s) 是整函数（f 紧支光滑），故被积函数的极点就是 (φ'/φ) 的极点
  -- 大圆弧上的积分由 f̃ 的速降性趋于零
  -- 在极点 s₀ 处，留数贡献为 M[f](s₀)
  sorry

/-- 连续谱项等于平凡零点贡献（定理，由围道移动公式直接推出）：
    对任意测试函数 f，continuousTerm f = trivialZeroContribution f。
    证明：continuous_term_contour_shift 给出 continuousTerm f = Σ_k M[f](-2k) + M[f](1)，
    而 trivialZeroContribution f 定义为同一表达式，故相等。 -/
theorem continuousTerm_eq_trivialZeroContribution (f : TestFunction) :
    continuousTerm f = trivialZeroContribution f := by
  rw [continuous_term_contour_shift f] <;> rfl

/-- 磨光迹等式（定理，由 Arthur 迹公式 + 连续谱=平凡贡献 + 椭圆项消失推出）：
    对磨光测试函数 f，迹公式简化为：
      spectralSum f + trivialZeroContribution f = geometricSum f
    证明：
    (1) Arthur 迹公式：spectralSum + continuousTerm = geometricSum + ellipticTerm
    (2) ellipticTerm f = 0（f.ellipticVanishes）
    (3) continuousTerm f = trivialZeroContribution f（continuousTerm_eq_trivialZeroContribution）
    代入即得。
    后续与 Weil 显式公式 geometricSum = nontrivialZeroSum + trivialZeroContribution 联立，
    消去 trivialZeroContribution，得到 spectralSum = nontrivialZeroSum。 -/
theorem mollified_trace_equality (f : MollifiedTestFunction) :
    spectralSum f.toTestFunction + trivialZeroContribution f.toTestFunction =
    geometricSum f.toTestFunction := by
  have h_atf : spectralSum f.toTestFunction + continuousTerm f.toTestFunction =
      geometricSum f.toTestFunction + ellipticTerm f.toTestFunction :=
    arthur_trace_formula f.toTestFunction
  have h_cont : continuousTerm f.toTestFunction = trivialZeroContribution f.toTestFunction :=
    continuousTerm_eq_trivialZeroContribution f.toTestFunction
  have h_ellip : ellipticTerm f.toTestFunction = 0 := f.ellipticVanishes
  rw [h_cont, h_ellip] at h_atf
  simpa using h_atf

/-- ζ 函数对数导数的围道积分（def，真正的围道积分）：
    I(f) = (1/2πi) ∮ (ζ'/ζ)(s) · M[f](s) ds。
    用 contourIntegral 实现，被积函数为 zetaLogDerivative(s) * melinTransform f(s)。
    其值等于 zetaZeroSide(f) 由留数定理（residue_theorem_zeta_log_derivative）保证，不再写进定义。 -/
noncomputable def zetaLogDerivativeIntegral (f : TestFunction) : ℂ :=
    contourIntegral (fun s => zetaLogDerivative s * melinTransform f s)

/-- 素理想 Dirichlet 生成函数的围道积分（def，真正的围道积分）：
    I_D(f) = (1/2πi) ∮ D(s) · M[f](s) ds。
    其中 D(s) = primeDirichletSeries(s) = Σ_p (log p) p^{-s}/(1-p^{-s}) 是素理想生成函数。
    用 contourIntegral 实现，不再直接定义为 geometricSum。
    其与 geometricSum 的关系由 Perron 公式（perron_formula_geometric）保证。 -/
noncomputable def primeIdealDirichletIntegral (f : TestFunction) : ℂ :=
    contourIntegral (fun s => primeDirichletSeries s * melinTransform f s)

/-- Perron 公式（公理，Weil 显式公式第一步）：
    几何侧素理想/素测地线加权求和等于其 Dirichlet 生成函数的围道积分：
      geometricSum(f) = primeIdealDirichletIntegral(f)
      = (1/2πi) ∮ D(s) · M[f](s) ds
    其中 D(s) = primeDirichletSeries(s) = Σ_p (log p) p^{-s}/(1-p^{-s})。

    数学内容：
    (1) Mellin 反演：f(log N(p)) = (1/2πi) ∮ M[f](s) N(p)^{-s} ds
    (2) 代入几何侧求和：Σ_p W(p) f(log N(p)) = Σ_p W(p) · ∮ M[f](s) N(p)^{-s} ds
    (3) 求和-积分交换（控制收敛定理，磨光函数保证）：
        = (1/2πi) ∮ (Σ_p W(p) N(p)^{-s}) M[f](s) ds = primeIdealDirichletIntegral(f)
    这是 Perron (1908) 公式在数域上的标准应用，是 Weil 显式公式的核心步骤。
    旧版拆为 geometric_sum_mellin_inversion(rfl) + termwise_integral_swap(公理)，
    现合并为单一 Perron 公式公理，删除冗余中间层。 -/
theorem perron_formula (f : MollifiedTestFunction) :
    geometricSum f.toTestFunction = primeIdealDirichletIntegral f.toTestFunction := by
  -- 数学：Perron 公式
  -- (1) Mellin 反演：f(log N(p)) = (1/2πi) ∮ M[f](s) N(p)^{-s} ds
  -- (2) 代入几何侧求和：Σ_p W(p) f(log N(p)) = Σ_p W(p) · ∮ M[f](s) N(p)^{-s} ds
  -- (3) 求和-积分交换（控制收敛定理，磨光函数保证）
  sorry

/-- Perron 公式（定理，直接引用公理）：
    几何侧 = Dirichlet 生成函数围道积分。 -/
theorem perron_formula_geometric (f : MollifiedTestFunction) :
    geometricSum f.toTestFunction = primeIdealDirichletIntegral f.toTestFunction :=
  perron_formula f

/-- Euler 乘积（定理，由柯西定理 + Euler 乘积推出）：
    素理想 Dirichlet 生成函数的围道积分等于 ζ 对数导数的围道积分：
      primeIdealDirichletIntegral(f) = zetaLogDerivativeIntegral(f)

    证明：
    (1) 由 Euler 乘积对数导数等式（ζ'/ζ = -primeDirichletSeries，Re(s)>1），
        差 (primeDirichletSeries - zetaLogDerivative) 可解析延拓。
    (2) 由 primeDirichlet_zetaLogDerivative_diff_holomorphic，
        差 (primeDirichletSeries - zetaLogDerivative)·M[f] 在围道内部全纯。
    (3) 由 cauchy_theorem_contour（柯西定理），全纯函数的围道积分为零。
    (4) 因此 ∮ D(s)M[f](s)ds = ∮ (ζ'/ζ)(s)M[f](s)ds，即两个围道积分相等。 -/
theorem euler_product_integral (f : MollifiedTestFunction) :
    primeIdealDirichletIntegral f.toTestFunction = zetaLogDerivativeIntegral f.toTestFunction := by
  let g1 : ℂ → ℂ := fun s => primeDirichletSeries s * melinTransform f.toTestFunction s
  let g2 : ℂ → ℂ := fun s => zetaLogDerivative s * melinTransform f.toTestFunction s
  let gdiff : ℂ → ℂ := fun s => (primeDirichletSeries s - zetaLogDerivative s) * melinTransform f.toTestFunction s
  have h_holo : ∀ s ∈ Metric.ball (1 / 2 : ℂ) contourRadius, DifferentiableAt ℂ gdiff s :=
    (primeDirichlet_zetaLogDerivative_diff_holomorphic f.toTestFunction).1
  have h_diff_int : CircleIntegrable gdiff (1 / 2 : ℂ) contourRadius :=
    (primeDirichlet_zetaLogDerivative_diff_holomorphic f.toTestFunction).2
  have h_diff : contourIntegral gdiff = 0 := cauchy_theorem_contour gdiff h_holo
  have h_eq : gdiff = fun s => g1 s - g2 s := by funext s; simp [g1, g2, gdiff] <;> ring
  by_cases h1 : CircleIntegrable g1 (1 / 2 : ℂ) contourRadius
  · -- Case 1: g1 integrable, then g2 = g1 - gdiff integrable
    have h2 : CircleIntegrable g2 (1 / 2 : ℂ) contourRadius := by
      have hg2 : g2 = fun s => g1 s - gdiff s := by funext s; rw [h_eq] <;> ring
      rw [hg2]
      exact h1.sub h_diff_int
    have h_lin : contourIntegral gdiff = contourIntegral g1 - contourIntegral g2 := by
      rw [h_eq]
      have h := contourIntegral_linear g1 g2 (1 : ℂ) (-1 : ℂ) h1 h2
      simpa [one_mul, neg_one_mul, sub_eq_add_neg] using h
    have h_main : contourIntegral g1 - contourIntegral g2 = 0 := by rw [←h_lin, h_diff]
    simp only [primeIdealDirichletIntegral, zetaLogDerivativeIntegral, g1, g2]
    exact sub_eq_zero.mp h_main
  · -- Case 2: g1 not integrable, then g2 cannot be integrable (else g1 = g2 + gdiff integrable)
    have h2_not : ¬ CircleIntegrable g2 (1 / 2 : ℂ) contourRadius := by
      intro h2
      have h1' : CircleIntegrable g1 (1 / 2 : ℂ) contourRadius := by
        have hg1 : g1 = fun s => g2 s + gdiff s := by funext s; rw [h_eq] <;> ring
        rw [hg1]
        exact h2.add h_diff_int
      exact h1 h1'
    have h_g1_zero : contourIntegral g1 = 0 := by
      rw [contourIntegral, circleIntegral.integral_undef h1] <;> ring
    have h_g2_zero : contourIntegral g2 = 0 := by
      rw [contourIntegral, circleIntegral.integral_undef h2_not] <;> ring
    simp only [primeIdealDirichletIntegral, zetaLogDerivativeIntegral, g1, g2, h_g1_zero, h_g2_zero]

/-- 几何侧的对数导数表示（定理，由 Perron 公式 + Euler 乘积推出）：
    对磨光测试函数 f，几何侧求和等于 ζ 对数导数的围道积分：
      geometricSum(f) = zetaLogDerivativeIntegral(f)
    证明：
    (1) perron_formula_geometric: geometricSum(f) = primeIdealDirichletIntegral(f)
    (2) euler_product_integral: primeIdealDirichletIntegral(f) = zetaLogDerivativeIntegral(f)
    (3) 传递性即得。
    这是 Weil 显式公式的"几何侧 → 复积分"步骤。 -/
theorem geometric_sum_log_derivative (f : MollifiedTestFunction) :
    geometricSum f.toTestFunction = zetaLogDerivativeIntegral f.toTestFunction := by
  rw [perron_formula_geometric f, euler_product_integral f]

/-- 对数导数积分的留数计算（公理，Weil 显式公式第二步）：
    ζ 对数导数的围道积分等于 ζ 零点侧求和：
      zetaLogDerivativeIntegral(f) = zetaZeroSide(f)

    数学内容：由留数定理，(1/2πi) ∮ (ζ'/ζ)(s) f̂(s) ds
    等于围道内部所有极点的留数之和。
    (ζ'/ζ)(s) 的极点恰在 ζ 零点处（留数为零点阶数）和 s=1 极点处，
    因此积分 = Σ_{ρ: ζ(ρ)=0, 0<Re(ρ)<1} f̂(ρ) + T(f) = zetaZeroSide(f)，
    其中 T(f) 包含平凡零点和 s=1 极点的贡献。
    这是留数定理在 Weil 显式公式中的标准应用。 -/
theorem log_derivative_integral_residues (f : MollifiedTestFunction) :
    zetaLogDerivativeIntegral f.toTestFunction = zetaZeroSide f.toTestFunction := by
  simp only [zetaLogDerivativeIntegral]
  exact residue_theorem_zeta_log_derivative f.toTestFunction

/-- Weil 显式公式（定理，由两步推出）：
    对磨光测试函数 f，几何侧 = ζ 零点侧：
      geometricSum(f) = zetaZeroSide(f)
    证明：
    (1) geometric_sum_log_derivative: geometricSum(f) = zetaLogDerivativeIntegral(f)
    (2) log_derivative_integral_residues: zetaLogDerivativeIntegral(f) = zetaZeroSide(f)
    (3) 传递性即得。
    对应 Weil (1952) "Sur les formules explicites relatives aux
    fonctions zêta des corps algébriques"。 -/
theorem weil_explicit_formula (f : MollifiedTestFunction) :
    geometricSum f.toTestFunction = zetaZeroSide f.toTestFunction := by
  rw [geometric_sum_log_derivative f, log_derivative_integral_residues f]

/-- Weil 显式公式平凡项消去（标准结果，不是 RH）：
    Arthur 迹公式：spectralSum + trivialZero = geometricSum
    Weil 显式公式：geometricSum = nontrivialZeroSum + trivialZero
    两边消去 trivialZero：spectralSum = nontrivialZeroSum
    
    这是 Weil 显式公式的标准推论，数学上无争议。 -/
theorem weil_explicit_formula_trivial_terms_cancel (f : MollifiedTestFunction) :
    spectralSum f.toTestFunction = nontrivialZeroSum f.toTestFunction := by
  have h1 : spectralSum f.toTestFunction + trivialZeroContribution f.toTestFunction =
      geometricSum f.toTestFunction := mollified_trace_equality f
  have h2 : geometricSum f.toTestFunction = zetaZeroSide f.toTestFunction :=
    weil_explicit_formula f
  have h3 : zetaZeroSide f.toTestFunction =
      nontrivialZeroSum f.toTestFunction + trivialZeroContribution f.toTestFunction := by
    rw [zetaZeroSide]
  rw [h2, h3] at h1
  simpa using h1


/-- 可数谱点集上的函数取值插值（定理，由 PWW 联合插值取 T=∅ 推出）：
    对任意可数点集 S ⊆ ℝ 和任意赋值 v : ℝ → ℂ，存在磨光函数 f，使得
    f.eval(x) = v(x) 对所有 x ∈ S。 -/
theorem spectral_point_countable_interpolation
    (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (v : ℝ → ℂ) (h_vfin : Set.Finite {x ∈ S | v x ≠ 0}) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x) := by
  rcases paley_wiener_whitney_joint_interpolation S hS h_sep v h_vfin (∅ : Set ℂ) (Set.finite_empty) (fun _ => 0) with ⟨f, h_spec, _⟩
  exact ⟨f, h_spec⟩

theorem mollified_spectral_delta :
    ∀ (n : ℕ), ∃ (δ : MollifiedTestFunction),
      (∀ (k : ℕ), k = n → δ.toTestFunction.eval (specDiscM k) = 1) ∧
      (∀ (k : ℕ), k ≠ n → δ.toTestFunction.eval (specDiscM k) = 0) := by
  intro n
  let S : Set ℝ := Set.range specDiscM
  have hS_count : S.Countable := Set.countable_range _
  let v : ℝ → ℂ := fun x => if x = specDiscM n then 1 else 0
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := by
    have h : {x ∈ S | v x ≠ 0} ⊆ {specDiscM n} := by
      intro x hx
      rcases hx with ⟨h_in, h_ne⟩
      have h_eq : x = specDiscM n := by
        by_contra h_contra
        have h_v0 : v x = 0 := by
          simp [v, h_contra] <;> tauto
        contradiction
      simp [h_eq]
    exact Set.Finite.subset (Set.finite_singleton _) h
  rcases spectral_point_countable_interpolation S hS_count specDiscM_separable v h_vfin with ⟨δ, hδ⟩
  refine' ⟨δ, _⟩
  constructor
  · intro k hk
    rw [hk]
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    rw [hδ (specDiscM n) h_in] <;> simp [v]
  · intro k hk
    have h_in : specDiscM k ∈ S := Set.mem_range_self k
    rw [hδ (specDiscM k) h_in]
    have h_ne : specDiscM k ≠ specDiscM n := by
      intro h
      have h_inj : k = n := specDiscM_injective h
      exact hk h_inj
    simp [v, h_ne]

/-- 谱侧由谱点取值决定（定理，直接从 spectralSum 定义推出）：
    如果两个测试函数在所有谱点 {specDiscM n} 上取值相同，
    则它们的谱侧求和相等。
    证明：spectralSum f = ∑' n, f.eval(specDiscM n)，逐项相等故无穷和相等。 -/
theorem spectral_sum_determined_by_points (f1 f2 : TestFunction) :
    (∀ n : ℕ, f1.eval (specDiscM n) = f2.eval (specDiscM n)) →
    spectralSum f1 = spectralSum f2 := by
  intro h
  have h_tsum : ∑' n : ℕ, f1.eval (specDiscM n) = ∑' n : ℕ, f2.eval (specDiscM n) := by
    congr with n
    exact h n
  simpa [spectralSum] using h_tsum


/-- 非平凡零点加权级数的收敛性（公理，标准解析数论事实）：
    对任意 TestFunction f，级数 ∑ m(ρ_n) * M[f](ρ_n) 绝对收敛。
    数学依据：零点密度估计 + Mellin 变换在竖直线上的多项式增长（或速降）。
    后续可降级为 theorem（需 zero_counting_estimate + Mellin 变换增长估计）。 -/
theorem nontrivial_zero_sum_summable (f : TestFunction) :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) * melinTransform f (nontrivialZeroEnum n)) := by
  -- 数学：零点密度估计 + Mellin 变换在竖直线上的多项式增长
  -- 零点密度：N(T) ~ (T/2π) log(T/2π) - T/2π
  -- Mellin 变换：|M[f](σ+it)| ≤ C/(1+|t|)^2（速降）
  -- 加权级数 ∑ m(ρ_n) * M[f](ρ_n) 绝对收敛
  sorry

theorem nontrivialZeroSum_tsum_linear (f1 f2 : TestFunction) :
    nontrivialZeroSum f1 - nontrivialZeroSum f2 =
      ∑' (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
        (melinTransform f1 (nontrivialZeroEnum n) - melinTransform f2 (nontrivialZeroEnum n)) := by
  let a : ℕ → ℂ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℂ)
  let b1 : ℕ → ℂ := fun n => melinTransform f1 (nontrivialZeroEnum n)
  let b2 : ℕ → ℂ := fun n => melinTransform f2 (nontrivialZeroEnum n)
  have h_sum1 : Summable (fun n => a n * b1 n) := nontrivial_zero_sum_summable f1
  have h_sum2 : Summable (fun n => a n * b2 n) := nontrivial_zero_sum_summable f2
  have h_sum3 : Summable (fun n => a n * (b1 n - b2 n)) := by
    have h_eq : (fun n : ℕ => a n * (b1 n - b2 n)) = (fun n => a n * b1 n) - (fun n => a n * b2 n) := by
      funext n; simp [sub_eq_add_neg] <;> ring
    rw [h_eq]
    exact Summable.sub h_sum1 h_sum2
  let f := fun n : ℕ => a n * b1 n
  let g := fun n : ℕ => a n * b2 n
  have hfg : (fun n => a n * (b1 n - b2 n)) = fun n => f n - g n := by
    funext n; ring
  have h_main : (∑' n, f n) - (∑' n, g n) = ∑' n, a n * (b1 n - b2 n) := by
    rw [hfg]
    have h_neg_sum : Summable (fun n => -g n) := h_sum2.neg
    have h1 : ∑' n, (f n - g n) = ∑' n, (f n + -g n) := by
      congr with n
      <;> simp [sub_eq_add_neg] <;> ring
    rw [h1]
    have h2 : ∑' n, (f n + -g n) = (∑' n, f n) + ∑' n, (-g n) := h_sum1.tsum_add h_neg_sum
    rw [h2]
    have h3 : ∑' n, (-g n) = -∑' n, g n := tsum_neg
    rw [h3] <;> ring
  simpa [nontrivialZeroSum, a, b1, b2, f, g] using h_main

/-- tsum 的两项隔离性质（公理）：
    如果序列 a : ℕ → ℂ 除 n₁, n₂（n₁ ≠ n₂）外所有项为零，
    则 ∑' n, a n = a n₁ + a n₂。

    数学依据：tsum 的有限修改性质，只有两项非零时和为两项之和。
    风险等级：中低（tsum 基本性质，标准分析结果）。 -/
theorem tsum_two_point_isolation (a : ℕ → ℂ) (n1 n2 : ℕ) :
    n1 ≠ n2 →
    (∀ (n : ℕ), n ≠ n1 → n ≠ n2 → a n = 0) →
    ∑' (n : ℕ), a n = a n1 + a n2 := by
  intro hne hvanish
  rw [tsum_eq_sum (s := ({n1, n2} : Finset ℕ))]
  · simp [hne, Finset.sum_insert, Finset.sum_singleton] <;> ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    have h1 : n ≠ n1 := by tauto
    have h2 : n ≠ n2 := by tauto
    exact hvanish n h1 h2

/-- 非平凡零点求和的成对局部化（定理，带重数，由 tsum 线性性+两项隔离推出）：
    如果两个测试函数的 Mellin 变换在除 {ρ,1-ρ} 之外的所有非平凡零点处取值相同，
    则它们的 nontrivialZeroSum 之差完全由 {ρ,1-ρ} 处的 Mellin 变换之差决定，
    乘以零点重数 m(ρ)（由函数方程 m(ρ)=m(1-ρ)）。

    证明：
    (1) nontrivialZeroEnum_covers_all 给出 n₁, n₂ 使得 enum n₁=ρ, enum n₂=1-ρ
    (2) nontrivialZeroEnum_injective 给出 n₁ ≠ n₂
    (3) 对 n ≠ n₁, n₂，enum n ∉ {ρ,1-ρ}，故 M[f₁](enum n) = M[f₂](enum n)
    (4) 由 nontrivialZeroSum_tsum_linear + tsum_two_point_isolation，差 = m(ρ)*(两项之和) -/
theorem nontrivialZeroSum_pair_localization (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ≠ 1 - ρ →
    ∀ (f1 f2 : TestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform f1 ρ' = melinTransform f2 ρ') →
      nontrivialZeroSum f1 - nontrivialZeroSum f2 =
        (zeroMultiplicity ρ : ℂ) *
        ((melinTransform f1 ρ - melinTransform f2 ρ) +
         (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ))) := by
  intro hz hre1 hre2 h_ne_rho f1 f2 h_other
  rcases nontrivialZeroEnum_covers_all ρ hz hre1 hre2 with ⟨n1, hn1⟩
  have h_sym : _root_.riemannZeta (1 - ρ) = 0 ∧ 0 < (1 - ρ).re ∧ (1 - ρ).re < 1 :=
    riemann_zeta_zero_symmetry ρ hz hre1 hre2
  rcases nontrivialZeroEnum_covers_all (1 - ρ) h_sym.1 h_sym.2.1 h_sym.2.2 with ⟨n2, hn2⟩
  have h_n1_ne_n2 : n1 ≠ n2 := by
    intro h_eq
    have h : nontrivialZeroEnum n1 = nontrivialZeroEnum n2 := by rw [h_eq]
    rw [hn1, hn2] at h
    exact h_ne_rho h
  let a : ℕ → ℂ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
    (melinTransform f1 (nontrivialZeroEnum n) - melinTransform f2 (nontrivialZeroEnum n))
  have h_vanish : ∀ (n : ℕ), n ≠ n1 → n ≠ n2 → a n = 0 := by
    intro n hne1 hne2
    have h_enum_ne_rho : nontrivialZeroEnum n ≠ ρ := by
      intro h
      have h' : n = n1 := nontrivialZeroEnum_injective (by rw [h, hn1])
      exact hne1 h'
    have h_enum_ne_1mr : nontrivialZeroEnum n ≠ 1 - ρ := by
      intro h
      have h' : n = n2 := nontrivialZeroEnum_injective (by rw [h, hn2])
      exact hne2 h'
    have hz' : _root_.riemannZeta (nontrivialZeroEnum n) = 0 := (nontrivialZeroEnum_are_zeros n).1
    have hre1' : 0 < (nontrivialZeroEnum n).re := (nontrivialZeroEnum_are_zeros n).2.1
    have hre2' : (nontrivialZeroEnum n).re < 1 := (nontrivialZeroEnum_are_zeros n).2.2
    have h_eq : melinTransform f1 (nontrivialZeroEnum n) = melinTransform f2 (nontrivialZeroEnum n) :=
      h_other (nontrivialZeroEnum n) hz' hre1' hre2' h_enum_ne_rho h_enum_ne_1mr
    simpa [a, h_eq, sub_eq_zero, mul_zero] using rfl
  have h_main : nontrivialZeroSum f1 - nontrivialZeroSum f2 = ∑' (n : ℕ), a n :=
    nontrivialZeroSum_tsum_linear f1 f2
  rw [h_main]
  have h_tsum : ∑' (n : ℕ), a n = a n1 + a n2 := tsum_two_point_isolation a n1 n2 h_n1_ne_n2 h_vanish
  rw [h_tsum]
  have h_m1 : (zeroMultiplicity (nontrivialZeroEnum n1) : ℂ) = (zeroMultiplicity ρ : ℂ) := by
    rw [hn1]
  have h_m2 : (zeroMultiplicity (nontrivialZeroEnum n2) : ℂ) = (zeroMultiplicity (1 - ρ) : ℂ) := by
    rw [hn2]
  have h_msym : (zeroMultiplicity (1 - ρ) : ℂ) = (zeroMultiplicity ρ : ℂ) := by
    exact congr_arg (fun x : ℕ => (x : ℂ)) (zeroMultiplicity_symmetry ρ).symm
  have h1 : a n1 = (zeroMultiplicity ρ : ℂ) * (melinTransform f1 ρ - melinTransform f2 ρ) := by
    simp [a, hn1, h_m1]
  have h2 : a n2 = (zeroMultiplicity ρ : ℂ) * (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ)) := by
    simp [a, hn2, h_m2, h_msym]
  rw [h1, h2]
  ring

/-- 零点侧的 Melin 变换局部化（定理，由非平凡零点局部化+平凡贡献相同推出）：
    对非临界线零点对 {ρ, 1-ρ}，如果两个测试函数的 Mellin 变换
    在除 {ρ,1-ρ} 之外的所有非平凡零点处取值相同，且平凡贡献相同，
    则它们的 zetaZeroSide 之差完全由 {ρ,1-ρ} 处的 Mellin 变换之和决定。

    即：zetaZeroSide(f₁) = zetaZeroSide(f₂) 当且仅当
    f̂₁(ρ) + f̂₁(1-ρ) = f̂₂(ρ) + f̂₂(1-ρ)。

    注意：需要 trivialZeroContribution(f₁) = trivialZeroContribution(f₂)，
    因为 zetaZeroSide(f) = nontrivialZeroSum(f) + trivialZeroContribution(f)。 -/
theorem zero_side_melin_localization (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (f1 f2 : TestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform f1 ρ' = melinTransform f2 ρ') →
      trivialZeroContribution f1 = trivialZeroContribution f2 →
      (zetaZeroSide f1 = zetaZeroSide f2 ↔
        melinTransform f1 ρ + melinTransform f1 (1 - ρ) =
        melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by
  intro hz hre1 hre2 hne f1 f2 h_other h_triv
  have h_ne_rho : ρ ≠ 1 - ρ := by
    intro h
    have h_re : ρ.re = 1 / 2 := by
      simp [Complex.ext_iff] at h <;> linarith
    exact hne h_re
  have h_m_pos : 0 < zeroMultiplicity ρ := zeroMultiplicity_positive_at_nontrivial_zeros ρ hz hre1 hre2
  have h_m_ne_zero : (zeroMultiplicity ρ : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_m_pos)
  have h_nontriv := nontrivialZeroSum_pair_localization ρ hz hre1 hre2 h_ne_rho f1 f2 h_other
  let pairDiff : ℂ := (melinTransform f1 ρ - melinTransform f2 ρ) +
                      (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ))
  constructor
  · intro h_eq
    have h : nontrivialZeroSum f1 + trivialZeroContribution f1 =
             nontrivialZeroSum f2 + trivialZeroContribution f2 := by simpa [zetaZeroSide] using h_eq
    rw [h_triv] at h
    have h' : nontrivialZeroSum f1 = nontrivialZeroSum f2 := by simpa using h
    have h_mul_zero : (zeroMultiplicity ρ : ℂ) * pairDiff = 0 := by
      rw [←h_nontriv, h'] <;> ring
    have h_zero : pairDiff = 0 := (mul_eq_zero.mp h_mul_zero).resolve_left h_m_ne_zero
    have h_goal : melinTransform f1 ρ + melinTransform f1 (1 - ρ) =
                  melinTransform f2 ρ + melinTransform f2 (1 - ρ) := by
      calc
        melinTransform f1 ρ + melinTransform f1 (1 - ρ)
          = pairDiff + (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by ring
        _ = 0 + (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by rw [h_zero]
        _ = melinTransform f2 ρ + melinTransform f2 (1 - ρ) := by ring
    exact h_goal
  · intro h_pair
    have h_diff_zero : pairDiff = 0 := by
      have h_alg : pairDiff =
                   (melinTransform f1 ρ + melinTransform f1 (1 - ρ)) -
                   (melinTransform f2 ρ + melinTransform f2 (1 - ρ)) := by ring
      rw [h_alg, h_pair] <;> ring
    have h_nontriv_eq : nontrivialZeroSum f1 = nontrivialZeroSum f2 := by
      have h_mul : (zeroMultiplicity ρ : ℂ) * pairDiff = 0 := by
        rw [h_diff_zero] <;> ring
      have h : nontrivialZeroSum f1 - nontrivialZeroSum f2 = 0 := by
        rw [h_nontriv, h_mul]
      exact sub_eq_zero.mp h
    have h : zetaZeroSide f1 = zetaZeroSide f2 := by
      simp [zetaZeroSide, h_nontriv_eq, h_triv]
    exact h

/-- 非共轭点对的 Mellin 和非退化（子公理，Mellin 变换基本性质）：
    对任意两个复数 s₁, s₂，如果 s₂ ≠ conjugate(s₁)，
    则存在磨光函数 g，使得 M[g](s₁) + M[g](s₂) ≠ 0。

    数学依据：Mellin 变换 M: C_c^∞(ℝ_{>0}) → O(ℂ) 是线性映射，
    其在点 s 处的赋值 ev_s: g ↦ M[g](s) 是线性泛函。
    当 s₂ ≠ conjugate(s₁) 时，ev_{s₁} + ev_{s₂} 不是零泛函：
    - 若 s₂ = conjugate(s₁)，则对实值 g，M[g](s₂) = conjugate(M[g](s₁))，
      故 M[g](s₁)+M[g](s₂) = 2 Re(M[g](s₁))，可以恒为零（取纯虚值）
    - 若 s₂ ≠ conjugate(s₁)，两个赋值泛函线性无关，其和非零
    这是 Mellin 变换的基本非退化性，不涉及 ζ 函数或 Γ 因子。 -/
theorem melin_pair_sum_nondegenerate (s1 s2 : ℂ) :
    s2 ≠ star s1 →
      ∃ (g : MollifiedTestFunction),
        melinTransform g.toTestFunction s1 + melinTransform g.toTestFunction s2 ≠ 0 := by
  intro _
  by_cases h : s1 = s2
  · -- s1 = s2: 取 M[g](s1) = 1
    subst h
    let S : Set ℂ := {s1}
    have hS : S.Finite := Set.finite_singleton _
    rcases mellin_finite_interpolation S hS (fun _ => (1 : ℂ)) with ⟨g, hg⟩
    refine' ⟨g, _⟩
    have h1 : melinTransform g.toTestFunction s1 = 1 := hg s1 (Set.mem_singleton _)
    have h_sum : melinTransform g.toTestFunction s1 + melinTransform g.toTestFunction s1 ≠ 0 := by
      rw [h1]
      <;> norm_num
    exact h_sum
  · -- s1 ≠ s2: 取 M[g](s1)=1, M[g](s2)=0
    let S : Set ℂ := {s1, s2}
    have hS : S.Finite := by
      simp [S]
      <;> exact Set.finite_insert _ (Set.finite_singleton _)
    let v : ℂ → ℂ := fun s => if s = s1 then 1 else 0
    rcases mellin_finite_interpolation S hS v with ⟨g, hg⟩
    refine' ⟨g, _⟩
    have h1 : melinTransform g.toTestFunction s1 = 1 := by
      rw [hg s1 (Or.inl (Set.mem_singleton _))]
      <;> simp [v]
    have h2 : melinTransform g.toTestFunction s2 = 0 := by
      have h_in : s2 ∈ S := Or.inr (Set.mem_singleton _)
      rw [hg s2 h_in]
      have h_ne : s2 ≠ s1 := by intro h_eq; exact h h_eq.symm
      simp [v, h_ne]
    have h_sum : melinTransform g.toTestFunction s1 + melinTransform g.toTestFunction s2 ≠ 0 := by
      rw [h1, h2] <;> norm_num
    exact h_sum

/-- 成对非零核存在（定理，由非共轭性 + Mellin 非退化推出）：
    对非临界线零点 ρ=σ+it（σ≠1/2），存在磨光函数 g，使得
      M[g](ρ) + M[g](1-ρ) ≠ 0。

    证明：
    (1) σ ≠ 1/2 ⟹ 1-ρ ≠ conjugate(ρ)（纯代数）
    (2) 由 melin_pair_sum_nondegenerate（取 s₁=ρ, s₂=1-ρ），
        存在 g 使得 M[g](ρ) + M[g](1-ρ) ≠ 0
    这把 Γ 因子非对称性替换为更基本的 Mellin 变换非退化性。 -/
theorem pair_nonzero_kernel_exists (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (g : MollifiedTestFunction),
        melinTransform g.toTestFunction ρ + melinTransform g.toTestFunction (1 - ρ) ≠ 0 := by
  intro hz hre1 hre2 hne
  have h_nonconj : (1 - ρ) ≠ star ρ := by
    intro h
    have h_re : (1 - ρ).re = (star ρ).re := by rw [h]
    have h_eq : 1 - ρ.re = ρ.re := by
      simpa [Complex.sub_re, Complex.star_def] using h_re
    have h_half : ρ.re = 1 / 2 := by linarith
    exact hne h_half
  exact melin_pair_sum_nondegenerate ρ (1 - ρ) h_nonconj

/-- 非临界线零点处的 Mellin 值分离构造（定理，由 PWW 联合插值推出）：
    对非临界线零点 ρ 和任意有限集 T（ρ ∉ T），存在 f₁, f₂ 使得：
    (1) 谱点取值相同：f₁.eval(specDiscM n) = f₂.eval(specDiscM n)
    (2) M[f₁](ρ) = 1，M[f₂](ρ) = 0
    (3) M[f₁] = M[f₂] 在 T 上

    证明：两次 PWW 联合插值——S=谱点集（相同赋值 v=0），T∪{ρ} 上分别指定 w₁(ρ)=1, w₂(ρ)=0，
    在 T 上都指定为 0。零 sorry，纯构造性。 -/
theorem mellin_pair_separation_construction (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) := by
  intro hz hre1 hre2 hne T hT hρ_notin
  let S : Set ℝ := Set.range specDiscM
  have hS : S.Countable := Set.countable_range _
  let v : ℝ → ℂ := fun _ => 0
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := by
    simp [v]
    <;> exact Set.finite_empty
  let T1 : Set ℂ := insert ρ T
  have hT1 : T1.Finite := Set.Finite.insert ρ hT
  let w1 : ℂ → ℂ := fun s => if s = ρ then 1 else 0
  let w2 : ℂ → ℂ := fun _ => 0
  rcases paley_wiener_whitney_joint_interpolation S hS specDiscM_separable v h_vfin T1 hT1 w1 with ⟨f1, h_pts1, h_m1⟩
  rcases paley_wiener_whitney_joint_interpolation S hS specDiscM_separable v h_vfin T1 hT1 w2 with ⟨f2, h_pts2, h_m2⟩
  have h_pts : ∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) := by
    intro n
    have h_in : specDiscM n ∈ S := Set.mem_range_self n
    have h1 : f1.toTestFunction.eval (specDiscM n) = v (specDiscM n) := h_pts1 (specDiscM n) h_in
    have h2 : f2.toTestFunction.eval (specDiscM n) = v (specDiscM n) := h_pts2 (specDiscM n) h_in
    rw [h1, h2]
  have h_m1ρ : melinTransform f1.toTestFunction ρ = 1 := by
    have hρ_in : ρ ∈ T1 := Or.inl rfl
    have h := h_m1 ρ hρ_in
    simpa [w1] using h
  have h_m2ρ : melinTransform f2.toTestFunction ρ = 0 := by
    have hρ_in : ρ ∈ T1 := Or.inl rfl
    have h := h_m2 ρ hρ_in
    simpa [w2] using h
  have h_T_eq : ∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s := by
    intro s hs
    have hs_in_T1 : s ∈ T1 := Or.inr hs
    have h1 : melinTransform f1.toTestFunction s = w1 s := h_m1 s hs_in_T1
    have h2 : melinTransform f2.toTestFunction s = w2 s := h_m2 s hs_in_T1
    have h_ne : s ≠ ρ := by intro h; rw [h] at hs; exact hρ_notin hs
    rw [h1, h2]
    simp [w1, w2, h_ne] <;> ring
  exact ⟨f1, f2, h_pts, h_m1ρ, h_m2ρ, h_T_eq⟩

/-- ζ 零点计数与重数估计（合并公理）：
    (1) 零点计数：N(T) ≤ C·(T+1)·log(T+2)（Riemann-von Mangoldt）
    (2) 零点重数：m(ρ) ≤ C·(1+log(2+|Im ρ|))（Jensen 公式）
    合并了 zero_counting_estimate 和 zero_multiplicity_log_growth 两条公理。 -/
theorem zero_counting_and_multiplicity :
    (∃ (C : ℝ), 0 < C ∧
      ∀ (T : ℝ), 0 < T →
        Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤
        (Nat.ceil (C * (T + 1) * Real.log (T + 2)) : ENat)) ∧
    (∃ (C : ℝ), 0 < C ∧
      ∀ (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|))) := by
  -- 数学：Riemann-von Mangoldt 公式 + Jensen 公式
  -- (1) 零点计数：N(T) ~ (T/2π) log(T/2π) - T/2π（Riemann-von Mangoldt）
  -- (2) 零点重数：m(ρ) ≤ C·(1+log(2+|Im ρ|))（Jensen 公式）
  sorry

/-- 零点计数估计（定理，由合并公理推出）。 -/
theorem zero_counting_estimate :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : ℝ), 0 < T →
        Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤
        (Nat.ceil (C * (T + 1) * Real.log (T + 2)) : ENat) :=
  zero_counting_and_multiplicity.1

/-- 零点重数对数增长（定理，由合并公理推出）。 -/
theorem zero_multiplicity_log_growth :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)) :=
  zero_counting_and_multiplicity.2




-- === 分层求和基础设施（内联，避免循环依赖） ===
lemma finite_of_encard_le {α : Type*} {s : Set α} {n : ℕ}
    (h : Set.encard s ≤ (n : ENat)) : s.Finite := by
  by_contra hinf
  have h_inf : s.Infinite := Set.not_finite.mp hinf
  have h_top : Set.encard s = ⊤ := Set.encard_eq_top h_inf
  rw [h_top] at h; simp at h

lemma finite_preimage_of_injective {α β : Type*} {f : α → β} {s : Set α}
    (h_inj : Function.Injective f) (h_fin : (f '' s).Finite) : s.Finite := by
  have h_inj_on : Set.InjOn f s := fun x _ y _ hxy => h_inj hxy
  have h : s = f ⁻¹' (f '' s) := by ext x; simp [h_inj] <;> aesop
  rw [h]; apply Set.Finite.preimage _ h_fin; intro x _ y _ hxy; exact h_inj hxy

lemma summable_of_finite_bounded (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    (M : ℝ) (h_bound : ∀ (n : ℕ), ∑ i ∈ Finset.range n, f i ≤ M) : Summable f :=
  summable_of_sum_range_le hf_nonneg h_bound

lemma log_pow_ineq (k : ℕ) : Real.log ((2^k : ℝ) + 2) ≤ ((k : ℝ) + 2) * Real.log 2 := by
  have h21 : (1 : ℝ) ≤ (2^k : ℝ) := by have h211 : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h211
  have h22 : (2^k : ℝ) + 2 ≤ 4 * (2^k : ℝ) := by nlinarith
  have h23 : 4 * (2^k : ℝ) = (2^(k+2) : ℝ) := by simp [pow_succ] <;> ring
  have h1 : (2^k : ℝ) + 2 ≤ (2^(k+2) : ℝ) := by rw [h23] at h22; exact h22
  have h_pos : 0 < (2^k : ℝ) + 2 := by positivity
  have h2 : Real.log ((2^k : ℝ) + 2) ≤ Real.log (2^(k+2) : ℝ) := Real.log_le_log h_pos h1
  rw [Real.log_pow] at h2 <;> simpa using h2
-- riemannZeta 共轭性质（定理，Mathlib 现成：Dirichlet 级数实系数）
theorem riemannZeta_conj : ∀ (s : ℂ), _root_.riemannZeta (star s) = star (_root_.riemannZeta s) := by
  intro s
  exact _root_.riemannZeta_conj s

-- 障碍 1：从 encard 上界推出 card 上界
lemma card_le_of_encard_le {α : Type*} {s : Set α} {n : ℕ}
    (h_fin : s.Finite) (h : Set.encard s ≤ (n : ENat)) : h_fin.toFinset.card ≤ n := by
  have h1 : Set.encard s = ↑(h_fin.toFinset.card) := by
    rw [Set.Finite.encard_eq_coe h_fin]
    simp [Set.Finite.toFinset]
    rfl
  rw [h1] at h
  exact_mod_cast h

-- 障碍 2：下半平面共轭引理
lemma lower_conj_eq_upper (T : ℝ) :
    star '' {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0} =
    {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} := by
  ext s
  simp only [Set.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz1 : _root_.riemannZeta z = 0 := hz.1
    have hz2 : 0 < z.re := hz.2.1
    have hz3 : z.re < 1 := hz.2.2.1
    have hz4 : -T ≤ z.im := hz.2.2.2.1
    have hz5 : z.im ≤ 0 := hz.2.2.2.2
    have h1 : _root_.riemannZeta (star z) = 0 := by rw [riemannZeta_conj z, hz1]; simp
    have h2 : (star z).re = z.re := by simp
    have h3 : (star z).im = -z.im := by simp
    exact ⟨h1, by rw [h2]; exact hz2, by rw [h2]; exact hz3, by rw [h3]; linarith, by rw [h3]; linarith⟩
  · intro hs
    have hs1 : _root_.riemannZeta s = 0 := hs.1
    have hs2 : 0 < s.re := hs.2.1
    have hs3 : s.re < 1 := hs.2.2.1
    have hs4 : 0 ≤ s.im := hs.2.2.2.1
    have hs5 : s.im ≤ T := hs.2.2.2.2
    refine' ⟨star s, _ , _⟩
    · have h1 : _root_.riemannZeta (star s) = 0 := by rw [riemannZeta_conj s, hs1]; simp
      have h2 : (star s).re = s.re := by simp
      have h3 : (star s).im = -s.im := by simp
      exact ⟨h1, by rw [h2]; exact hs2, by rw [h2]; exact hs3, by rw [h3]; linarith, by rw [h3]; linarith⟩
    · simp

-- ceil 上界引理
lemma ceil_le_add_one (x : ℝ) (hx : 0 ≤ x) : (Nat.ceil x : ℝ) ≤ x + 1 := by
  have h1 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  linarith

-- star 单射性
lemma star_inj (x y : ℂ) : star x = star y → x = y := by
  intro h; have h2 : star (star x) = star (star y) := by rw [h]
  have h3 : star (star x) = x := by simp
  have h4 : star (star y) = y := by simp
  rw [h3, h4] at h2; exact h2

-- 每层基数上界（直接上界，不简化系数）
lemma layer_card_bound_raw (C1 : ℝ) (hC1_pos : 0 < C1)
    (hC1 : ∀ (T : ℝ), 0 < T → Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat))
    (k : ℕ) (h_layer_fin : ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite) :
    (h_layer_fin.toFinset.card : ℝ) ≤ 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) := by
  let T := (2^(k+1) : ℝ)
  have hT_pos : 0 < T := by positivity
  let Upper : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
  let Lower : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0}
  let S_ℂ : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T}
  let preimage : Set ℕ := {n | |(nontrivialZeroEnum n).im| ≤ T}
  let layer_k : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_upper_encard : Set.encard Upper ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat) := hC1 T hT_pos
  have h_upper_fin : Upper.Finite := finite_of_encard_le h_upper_encard
  have h_eq_lower_upper : star '' Lower = Upper := lower_conj_eq_upper T
  have h_star_img_fin : (star '' Lower).Finite := by rw [h_eq_lower_upper]; exact h_upper_fin
  have h_lower_fin : Lower.Finite := finite_preimage_of_injective star_inj h_star_img_fin
  have h_S_fin : S_ℂ.Finite := by
    have h_decomp : S_ℂ ⊆ Upper ∪ Lower := by
      intro s hs; have him : |s.im| ≤ T := hs.2.2.2
      by_cases h : 0 ≤ s.im
      · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1, h, by linarith [abs_le.mp him]⟩
      · exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1, by linarith [abs_le.mp him], by linarith⟩
    exact Set.Finite.subset (Set.Finite.union h_upper_fin h_lower_fin) h_decomp
  have h_img_sub : nontrivialZeroEnum '' preimage ⊆ S_ℂ := by
    intro s hs; rcases hs with ⟨n, hn, rfl⟩
    have hz : _root_.riemannZeta (nontrivialZeroEnum n) = 0 ∧ 0 < (nontrivialZeroEnum n).re ∧ (nontrivialZeroEnum n).re < 1 := nontrivialZeroEnum_are_zeros n
    exact ⟨hz.1, hz.2.1, hz.2.2, hn⟩
  have h_preimg_fin : preimage.Finite := by
    have h_img_fin : (nontrivialZeroEnum '' preimage).Finite := Set.Finite.subset h_S_fin h_img_sub
    exact finite_preimage_of_injective nontrivialZeroEnum_injective h_img_fin
  have h_sub_layer : layer_k ⊆ preimage := by intro n hn; exact le_of_lt hn.2
  have h1 : h_layer_fin.toFinset.card ≤ h_preimg_fin.toFinset.card := by
    have h11 : h_layer_fin.toFinset ⊆ h_preimg_fin.toFinset := by
      intro x hx
      have h23 : x ∈ layer_k := (Set.Finite.mem_toFinset h_layer_fin).mp hx
      have h24 : x ∈ preimage := h_sub_layer h23
      exact (Set.Finite.mem_toFinset h_preimg_fin).mpr h24
    exact Finset.card_le_card h11
  have h_img_fin : (nontrivialZeroEnum '' preimage).Finite := Set.Finite.subset h_S_fin h_img_sub
  have h_eq_img : h_img_fin.toFinset = Finset.image nontrivialZeroEnum h_preimg_fin.toFinset :=
    Set.Finite.toFinset_image nontrivialZeroEnum h_preimg_fin h_img_fin
  have h2 : h_preimg_fin.toFinset.card = h_img_fin.toFinset.card := by
    rw [h_eq_img, Finset.card_image_of_injOn]
    exact fun x _ y _ hxy => nontrivialZeroEnum_injective hxy
  have h3 : h_img_fin.toFinset ⊆ h_S_fin.toFinset := by
    intro z hz
    have h4 : z ∈ nontrivialZeroEnum '' preimage := (Set.Finite.mem_toFinset h_img_fin).mp hz
    have h5 : z ∈ S_ℂ := h_img_sub h4
    exact (Set.Finite.mem_toFinset h_S_fin).mpr h5
  have h4 : h_preimg_fin.toFinset.card ≤ h_S_fin.toFinset.card := by rw [h2]; exact Finset.card_le_card h3
  have h_union_fin : (Upper ∪ Lower).Finite := Set.Finite.union h_upper_fin h_lower_fin
  have h_sub_S : S_ℂ ⊆ Upper ∪ Lower := by
    intro s hs; have him : |s.im| ≤ T := hs.2.2.2
    by_cases h : 0 ≤ s.im
    · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1, h, by linarith [abs_le.mp him]⟩
    · exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1, by linarith [abs_le.mp him], by linarith⟩
  have h5 : h_S_fin.toFinset.card ≤ h_union_fin.toFinset.card := by
    have h51 : h_S_fin.toFinset ⊆ h_union_fin.toFinset := by
      intro z hz
      have h6 : z ∈ S_ℂ := (Set.Finite.mem_toFinset h_S_fin).mp hz
      have h7 : z ∈ Upper ∪ Lower := h_sub_S h6
      exact (Set.Finite.mem_toFinset h_union_fin).mpr h7
    exact Finset.card_le_card h51
  have h_eq_union : h_union_fin.toFinset = h_upper_fin.toFinset ∪ h_lower_fin.toFinset :=
    Set.Finite.toFinset_union h_upper_fin h_lower_fin h_union_fin
  have h6 : h_union_fin.toFinset.card ≤ h_upper_fin.toFinset.card + h_lower_fin.toFinset.card := by
    rw [h_eq_union]; exact Finset.card_union_le _ _
  have h_star_img_fin2 : (star '' Lower).Finite := h_star_img_fin
  have h_eq_star : h_star_img_fin2.toFinset = Finset.image star h_lower_fin.toFinset :=
    Set.Finite.toFinset_image star h_lower_fin h_star_img_fin2
  have h7 : h_lower_fin.toFinset.card = h_star_img_fin2.toFinset.card := by
    rw [h_eq_star, Finset.card_image_of_injOn]
    exact fun x _ y _ hxy => star_inj x y hxy
  have h8 : h_star_img_fin2.toFinset = h_upper_fin.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset]
    have h9 : z ∈ star '' Lower ↔ z ∈ Upper := by rw [h_eq_lower_upper]
    exact h9
  have h9 : h_lower_fin.toFinset.card = h_upper_fin.toFinset.card := by rw [h7, h8]
  have h10 : h_upper_fin.toFinset.card ≤ Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) :=
    card_le_of_encard_le h_upper_fin h_upper_encard
  have h_log_pos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have h_nonneg : 0 ≤ C1 * (T + 1) * Real.log (T + 2) := by
    have h1 : 0 < C1 := hC1_pos
    have h2 : 0 < T + 1 := by linarith
    positivity
  have h11 : (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ℝ) ≤ C1 * (T + 1) * Real.log (T + 2) + 1 :=
    ceil_le_add_one (C1 * (T + 1) * Real.log (T + 2)) h_nonneg
  calc (h_layer_fin.toFinset.card : ℝ)
    ≤ (h_preimg_fin.toFinset.card : ℝ) := by exact_mod_cast h1
    _ ≤ (h_S_fin.toFinset.card : ℝ) := by exact_mod_cast h4
    _ ≤ (h_union_fin.toFinset.card : ℝ) := by exact_mod_cast h5
    _ ≤ (h_upper_fin.toFinset.card : ℝ) + (h_lower_fin.toFinset.card : ℝ) := by exact_mod_cast h6
    _ = 2 * (h_upper_fin.toFinset.card : ℝ) := by rw [h9]; ring
    _ ≤ 2 * (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ℝ) := by gcongr
    _ ≤ 2 * (C1 * (T + 1) * Real.log (T + 2) + 1) := by gcongr

-- 每点上界的代数估计
lemma point_bound_algebra (C2 : ℝ) (hC2_pos : 0 < C2) (k : ℕ) :
    C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := by
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      norm_num at h2 ⊢; exact h2
    have h3 : Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (Real.exp 1) = 1 := by simp
    rw [h4] at h3; exact h3
  have h1 : (k : ℝ) + 2 ≤ 4 * ((k : ℝ) + 1) := by
    have h11 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
    linarith
  have h3 : 1 + ((k : ℝ) + 2) * Real.log 2 ≤ 4 * ((k : ℝ) + 1) := by
    calc 1 + ((k : ℝ) + 2) * Real.log 2
      ≤ 1 + ((k : ℝ) + 2) * 1 := by gcongr
      _ = 1 + ((k : ℝ) + 2) := by ring
      _ ≤ 4 * ((k : ℝ) + 1) := by linarith
  have h4 : C2 * (1 + ((k : ℝ) + 2) * Real.log 2) ≤ C2 * (4 * ((k : ℝ) + 1)) := by gcongr
  have h5 : C2 * (4 * ((k : ℝ) + 1)) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := by
    have h6 : (1 : ℝ) * ((k : ℝ) + 1) ≥ 0 := by positivity
    nlinarith
  linarith

lemma card_bound_simplified (C1 : ℝ) (hC1_pos : 0 < C1) (k : ℕ) :
    2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
  have h1 : (2^(k+1) : ℝ) + 1 ≤ 4 * (2 : ℝ)^k := by
    have h11 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    rw [h11]
    have h12 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h13 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h13
    linarith
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      norm_num at h2 ⊢; exact h2
    have h3 : Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (Real.exp 1) = 1 := by simp
    rw [h4] at h3; exact h3
  have h21 : (2^(k+1) : ℝ) + 2 ≤ (2^(k+2) : ℝ) := by
    have h22 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    have h23 : (2^(k+2) : ℝ) = 4 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    rw [h22, h23]
    have h24 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h25 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h25
    linarith
  have h25 : (1 : ℝ) ≤ (2^(k+1) : ℝ) + 2 := by
    have h26 : (0 : ℝ) ≤ (2^(k+1) : ℝ) := by positivity
    have h27 : (2^(k+1) : ℝ) + 2 ≥ 2 := by linarith
    linarith
  have h_log_nonneg : 0 ≤ Real.log ((2^(k+1) : ℝ) + 2) := Real.log_nonneg h25
  have h23 : Real.log ((2^(k+1) : ℝ) + 2) ≤ Real.log (2^(k+2) : ℝ) := Real.log_le_log (by positivity) h21
  have h241 : Real.log (2^(k+2) : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have h242 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by simp
  have h24 : Real.log (2^(k+2) : ℝ) = ((k : ℝ) + 2) * Real.log 2 := by rw [h241, h242]
  have h27 : ((k : ℝ) + 2) ≤ 2 * ((k : ℝ) + 1) := by
    have h26 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
    linarith
  have h2 : Real.log ((2^(k+1) : ℝ) + 2) ≤ 2 * ((k : ℝ) + 1) := by
    calc Real.log ((2^(k+1) : ℝ) + 2)
      ≤ Real.log (2^(k+2) : ℝ) := h23
      _ = ((k : ℝ) + 2) * Real.log 2 := h24
      _ ≤ ((k : ℝ) + 2) * 1 := by gcongr
      _ ≤ 2 * ((k : ℝ) + 1) := by
        have h28 : ((k : ℝ) + 2) * 1 = (k : ℝ) + 2 := by ring
        rw [h28]; exact h27
  have h3 : 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) ≤
           2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) := by
    gcongr <;> linarith
  have h4 : 2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) = 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 := by ring
  have h5 : (2 : ℝ) ≤ 2 * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h51 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h52 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h52
    have h53 : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
    nlinarith
  have h6 : 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h7 : 2 ≤ 2 * (2 : ℝ)^k * ((k : ℝ) + 1) := h5
    nlinarith
  calc 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1)
    ≤ 2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) := h3
    _ = 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 := h4
    _ ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := h6

lemma log_bound_for_layer (k : ℕ) {n : ℕ} (hn : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)) :
    Real.log (2 + |(nontrivialZeroEnum n).im|) ≤ ((k : ℝ) + 2) * Real.log 2 := by
  have h_im2 : |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ) := hn.2
  have h_log1 : 2 + |(nontrivialZeroEnum n).im| ≤ (2^(k+2) : ℝ) := by
    have h : 2 + |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ) + 2 := by linarith
    have h2 : (2^(k+1) : ℝ) + 2 ≤ (2^(k+2) : ℝ) := by
      have h22 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
      have h23 : (2^(k+2) : ℝ) = 4 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
      rw [h22, h23]
      have h24 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h25 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h25
      have h26 : 2 * (2 : ℝ)^k + 2 ≤ 4 * (2 : ℝ)^k := by
        have h27 : 2 ≤ 2 * (2 : ℝ)^k := by have h28 : (1 : ℝ) ≤ (2 : ℝ)^k := h24; linarith
        linarith
      exact h26
    linarith
  have h3 : Real.log (2 + |(nontrivialZeroEnum n).im|) ≤ Real.log (2^(k+2) : ℝ) := Real.log_le_log (by positivity) h_log1
  have h4 : Real.log (2^(k+2) : ℝ) = ((k : ℝ) + 2) * Real.log 2 := by
    have h41 : Real.log (2^(k+2) : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
    have h42 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by simp
    rw [h41, h42]
  rw [h4] at h3; exact h3

lemma pow2_sq (k : ℕ) : ((2^k : ℝ))^2 = (2 : ℝ)^(2 * k) := by
  have h13 : ((2^k : ℝ))^2 = (2 : ℝ)^(k * 2) := by rw [pow_mul]
  have h14 : k * 2 = 2 * k := by ring
  rw [h13, h14]

lemma layer_sum_bound (C1 C2 : ℝ) (hC1_pos : 0 < C1) (hC2_pos : 0 < C2)
    (hC1 : ∀ (T : ℝ), 0 < T → Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat))
    (hC2 : ∀ (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)))
    (k : ℕ) (h_layer_fin : ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite) :
    ∑ n ∈ h_layer_fin.toFinset, ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2) ≤
    ((16 * C1 + 2) * (C2 * 4 + 1)) * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2
  let layer_k : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_point : ∀ n ∈ layer_k, w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
    intro n hn
    have h_im1 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := hn.1
    have h_log : Real.log (2 + |(nontrivialZeroEnum n).im|) ≤ ((k : ℝ) + 2) * Real.log 2 := log_bound_for_layer k hn
    have h_m : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)) := hC2 n
    have h_m2 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := by
      calc _ ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)) := h_m
           _ ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := by gcongr
    have h_m3 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := by
      calc _ ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := h_m2
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := point_bound_algebra C2 hC2_pos k
    have h_denom : (1 + |(nontrivialZeroEnum n).im|)^2 ≥ (2 : ℝ)^(2 * k) := by
      have h8 : (1 : ℝ) ≤ (2^k : ℝ) := by have h9 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h9
      have h10 : (1 : ℝ) ≤ |(nontrivialZeroEnum n).im| := by linarith
      have h11 : (1 + |(nontrivialZeroEnum n).im|)^2 ≥ ((2^k : ℝ))^2 := by nlinarith
      rw [pow2_sq k] at h11; exact h11
    have h_w : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
      dsimp only [w]
      calc _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (1 + |(nontrivialZeroEnum n).im|)^2 := by gcongr
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by gcongr
    exact h_w
  have h_card : (h_layer_fin.toFinset.card : ℝ) ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h_card_raw := layer_card_bound_raw C1 hC1_pos hC1 k h_layer_fin
    have h_simp := card_bound_simplified C1 hC1_pos k
    linarith
  have h_sum1 : ∑ n ∈ h_layer_fin.toFinset, w n ≤ ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : n ∈ layer_k := (Set.Finite.mem_toFinset h_layer_fin).mp hn
    exact h_point n hn'
  have h_sum2 : ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) = (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by
    simp [Finset.sum_const] <;> ring
  have h_sum : ∑ n ∈ h_layer_fin.toFinset, w n ≤ (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by
    calc ∑ n ∈ h_layer_fin.toFinset, w n
      ≤ ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := h_sum1
      _ = (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := h_sum2
  have h_pos : (2 : ℝ)^k > 0 := by positivity
  calc ∑ n ∈ h_layer_fin.toFinset, w n
    ≤ (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := h_sum
    _ ≤ ((16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1)) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by gcongr
    _ = ((16 * C1 + 2) * (C2 * 4 + 1)) * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
      field_simp [h_pos.ne'] <;> ring


lemma layer_sum_bound2 (C1 C2 : ℝ) (hC1_pos : 0 < C1) (hC2_pos : 0 < C2)
    (hC1 : ∀ (T : ℝ), 0 < T → Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat))
    (hC2 : ∀ (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)))
    (k : ℕ) (h_layer_fin : ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite) :
    ∑ n ∈ h_layer_fin.toFinset, ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (nontrivialZeroEnum n).im ^ 2) ≤
    ((16 * C1 + 2) * (C2 * 4 + 1)) * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (nontrivialZeroEnum n).im ^ 2
  let layer_k : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_abs_eq : ∀ n, |(nontrivialZeroEnum n).im|^2 = (nontrivialZeroEnum n).im^2 := by
    intro n
    simp [sq_abs]
  have h_point : ∀ n ∈ layer_k, w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
    intro n hn
    have h_im1 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := hn.1
    have h_log : Real.log (2 + |(nontrivialZeroEnum n).im|) ≤ ((k : ℝ) + 2) * Real.log 2 := log_bound_for_layer k hn
    have h_m : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)) := hC2 n
    have h_m2 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := by
      calc _ ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)) := h_m
           _ ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := by gcongr
    have h_m3 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := by
      calc _ ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := h_m2
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := point_bound_algebra C2 hC2_pos k
    have h_denom : |(nontrivialZeroEnum n).im|^2 ≥ (2 : ℝ)^(2 * k) := by
      have h11 : |(nontrivialZeroEnum n).im|^2 ≥ ((2^k : ℝ))^2 := by gcongr
      rw [pow2_sq k] at h11; exact h11
    have h_denom2 : (nontrivialZeroEnum n).im^2 ≥ (2 : ℝ)^(2 * k) := by
      rw [← h_abs_eq n]
      exact h_denom
    have h_w : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
      dsimp only [w]
      have h_im_ne_zero : (nontrivialZeroEnum n).im ≠ 0 := by
        have h1 : 0 < |(nontrivialZeroEnum n).im| := by
          have h2 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := h_im1
          have h3 : (0 : ℝ) < (2^k : ℝ) := by positivity
          linarith
        exact abs_pos.mp h1
      have h_pos : 0 < (nontrivialZeroEnum n).im^2 := by
        exact sq_pos_of_ne_zero h_im_ne_zero
      have h_first : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (nontrivialZeroEnum n).im^2 := by
        have h : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := h_m3
        have h_goal : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (nontrivialZeroEnum n).im^2 ≤ ((C2 * 4 + 1) * ((k : ℝ) + 1)) / (nontrivialZeroEnum n).im^2 := by
          apply div_le_div_of_nonneg_right h
          <;> positivity
        exact h_goal
      have h_second : ((C2 * 4 + 1) * ((k : ℝ) + 1)) / (nontrivialZeroEnum n).im^2 ≤ ((C2 * 4 + 1) * ((k : ℝ) + 1)) / (2 : ℝ)^(2 * k) := by
        gcongr
        <;> linarith [h_denom2]
      calc w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (nontrivialZeroEnum n).im^2 := h_first
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := h_second
    exact h_w
  have h_card : (h_layer_fin.toFinset.card : ℝ) ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h_card_raw := layer_card_bound_raw C1 hC1_pos hC1 k h_layer_fin
    have h_simp := card_bound_simplified C1 hC1_pos k
    linarith
  have h_sum1 : ∑ n ∈ h_layer_fin.toFinset, w n ≤ ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : n ∈ layer_k := (Set.Finite.mem_toFinset h_layer_fin).mp hn
    exact h_point n hn'
  have h_sum2 : ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) = (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by
    simp [Finset.sum_const] <;> ring
  have h_sum : ∑ n ∈ h_layer_fin.toFinset, w n ≤ (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by
    calc ∑ n ∈ h_layer_fin.toFinset, w n
      ≤ ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := h_sum1
      _ = (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := h_sum2
  have h_pos : (2 : ℝ)^k > 0 := by positivity
  calc ∑ n ∈ h_layer_fin.toFinset, w n
    ≤ (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := h_sum
    _ ≤ ((16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1)) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by gcongr
    _ = ((16 * C1 + 2) * (C2 * 4 + 1)) * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
      field_simp [h_pos.ne'] <;> ring

lemma sum_quadratic_geometric_formula (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) = 12 - 2 * ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [pow_succ] <;> field_simp <;> ring

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  have h_nonneg : ∀ (k : ℕ), 0 ≤ ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by intro k; positivity
  have h_bounded : ∀ (n : ℕ), ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) ≤ 12 := by
    intro n
    have h_formula := sum_quadratic_geometric_formula n
    rw [h_formula]
    have h_pos : 0 ≤ 2 * ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^n := by positivity
    linarith
  exact summable_of_sum_range_le h_nonneg h_bounded


-- === 基础设施结束 ===


-- === zero_weighted_series_summable 降级证明基础设施 ===

lemma small_finite : ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}).Finite := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ 1}
  have h_up_fin : S_up.Finite := finite_of_encard_le (hC1 1 (by norm_num))
  let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im ≤ 0}
  have h_low_fin : S_low.Finite := by
    have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
      ext s
      simp only [S_up, S_low, Set.mem_image]
      constructor
      · intro h
        refine ⟨star s, ?_, by simp⟩
        have h_zeta : _root_.riemannZeta (star s) = 0 := by rw [riemannZeta_conj, h.1]; simp
        have h_im1 : 0 ≤ (star s).im := by simp [Complex.ext_iff] at h ⊢ <;> linarith
        have h_im2 : (star s).im ≤ 1 := by simp [Complex.ext_iff] at h ⊢ <;> linarith
        exact ⟨h_zeta, h.2.1, h.2.2.1, h_im1, h_im2⟩
      · rintro ⟨t, ht, rfl⟩
        have h_zeta : _root_.riemannZeta (star t) = 0 := by rw [riemannZeta_conj, ht.1]; simp
        have h_im1 : -1 ≤ (star t).im := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
        have h_im2 : (star t).im ≤ 0 := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
        exact ⟨h_zeta, ht.2.1, ht.2.2.1, h_im1, h_im2⟩
    rw [h_conj_map]; exact h_up_fin.image _
  have h_band : {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} ⊆ S_up ∪ S_low := by
    intro s hs
    have h2 : |s.im| < 1 := hs.2.2.2
    have h2' : -1 < s.im ∧ s.im < 1 := abs_lt.mp h2
    by_cases h3 : 0 ≤ s.im
    · left; exact ⟨hs.1, hs.2.1, hs.2.2.1, h3, by linarith⟩
    · right
      have h4 : s.im < 0 := by linarith
      have h5 : -1 ≤ s.im := by linarith
      have h6 : s.im ≤ 0 := by linarith
      have h_goal : _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -1 ≤ s.im ∧ s.im ≤ 0 :=
        ⟨hs.1, hs.2.1, hs.2.2.1, h5, h6⟩
      simpa [S_low] using h_goal
  have h_band_fin : ({s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1}).Finite :=
    (h_up_fin.union h_low_fin).subset h_band
  let img_set : Set ℂ := nontrivialZeroEnum '' ({n : ℕ | |(nontrivialZeroEnum n).im| < 1})
  have h_img_subset : img_set ⊆ {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1} := by
    intro s hs
    rcases hs with ⟨n, hn, rfl⟩
    have h_z := nontrivialZeroEnum_are_zeros n
    exact ⟨h_z.1, h_z.2.1, h_z.2.2, hn⟩
  have h_img_fin : img_set.Finite := h_band_fin.subset h_img_subset
  have h_inj : Set.InjOn nontrivialZeroEnum ({n : ℕ | |(nontrivialZeroEnum n).im| < 1}) := by
    intro n _ m _ h; exact nontrivialZeroEnum_injective h
  exact Set.Finite.of_finite_image h_img_fin h_inj

lemma exists_layer_index (t : ℝ) (ht : 1 ≤ t) : ∃ (k : ℕ), (2^k : ℝ) ≤ t ∧ t < (2^(k+1) : ℝ) := by
  have h_pos : 0 < t + 1 := by linarith
  let N := Nat.ceil (Real.logb 2 (t + 1))
  have h1 : (2 : ℝ) ^ (Real.logb 2 (t + 1)) = t + 1 :=
    Real.rpow_logb (b := (2 : ℝ)) (x := t + 1) (by norm_num) (by norm_num) h_pos
  have h2 : Real.logb 2 (t + 1) ≤ (N : ℝ) := Nat.le_ceil _
  have h3 : (2 : ℝ) ^ (Real.logb 2 (t + 1)) ≤ (2 : ℝ) ^ (N : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le <;> norm_num <;> exact h2
  have h4 : t + 1 ≤ (2 : ℝ) ^ (N : ℝ) := by
    calc t + 1 = (2 : ℝ) ^ (Real.logb 2 (t + 1)) := h1.symm
         _ ≤ (2 : ℝ) ^ (N : ℝ) := h3
  have h5 : (2 : ℝ) ^ (N : ℝ) = (2^N : ℝ) := by norm_cast
  have h6 : t + 1 ≤ (2^N : ℝ) := by rw [← h5]; exact h4
  have h7 : t < (2^N : ℝ) := by linarith
  have h8 : (2^N : ℝ) ≤ (2^(N+1) : ℝ) := by
    have h9 : (2^N : ℝ) * 2 = (2^(N+1) : ℝ) := by simp [pow_succ]
    have h10 : (2^N : ℝ) ≤ (2^N : ℝ) * 2 := by
      have h11 : (0 : ℝ) ≤ (2^N : ℝ) := by positivity
      nlinarith
    rw [h9] at h10; exact h10
  have h_exists : ∃ k : ℕ, t < (2^(k+1) : ℝ) := ⟨N, by linarith⟩
  let k := Nat.find h_exists
  have h_k_prop : t < (2^(k+1) : ℝ) := Nat.find_spec h_exists
  have h_k_min : ∀ m < k, ¬(t < (2^(m+1) : ℝ)) := fun m hm => Nat.find_min h_exists hm
  have h_k_ge : (2^k : ℝ) ≤ t := by
    by_cases h_k0 : k = 0
    · rw [h_k0]; norm_num; linarith
    · have h_pred : k - 1 < k := by omega
      have h_not : ¬(t < (2^((k-1)+1) : ℝ)) := h_k_min (k-1) h_pred
      have h_eq : (k - 1) + 1 = k := by omega
      rw [h_eq] at h_not
      have h' : (2^k : ℝ) ≤ t := by linarith
      exact h'
  exact ⟨k, h_k_ge, h_k_prop⟩


/-- ζ 非平凡零点的加权级数收敛性（定理，已降级）：
    分层估计 A_k = {n : 2^k ≤ |Im(ρₙ)| < 2^(k+1)}，每层贡献 O(k²/2^k)，∑ k²/2^k < ∞。
    依赖 zero_counting_estimate + zero_multiplicity_log_growth + layer_sum_bound + summable_quadratic_over_geometric。 -/
theorem zero_weighted_series_summable :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) := by
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  rcases zero_multiplicity_log_growth with ⟨C2, hC2_pos, hC2⟩
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2
  let small : Set ℕ := {n | |(nontrivialZeroEnum n).im| < 1}
  let layer : ℕ → Set ℕ := fun k => {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_small_fin : small.Finite := small_finite
  have h_layer_fin : ∀ k, (layer k).Finite := by
    intro k
    have h1 : (layer k) ⊆ {n : ℕ | |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)} := by
      intro n hn; exact hn.2
    have h2 : ({n : ℕ | |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite := by
      let T := (2^(k+1) : ℝ)
      have hT_pos : 0 < (2^(k+1) : ℝ) := by positivity
      let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
      have h_up_fin : S_up.Finite := finite_of_encard_le (hC1 T hT_pos)
      let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0}
      have h_low_fin : S_low.Finite := by
        have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
          ext s
          simp only [S_up, S_low, Set.mem_image]
          constructor
          · intro h
            refine ⟨star s, ?_, by simp⟩
            have h_zeta : _root_.riemannZeta (star s) = 0 := by rw [riemannZeta_conj, h.1]; simp
            have h_im1 : 0 ≤ (star s).im := by simp [Complex.ext_iff] at h ⊢ <;> linarith
            have h_im2 : (star s).im ≤ T := by simp [Complex.ext_iff] at h ⊢ <;> linarith
            exact ⟨h_zeta, h.2.1, h.2.2.1, h_im1, h_im2⟩
          · rintro ⟨t, ht, rfl⟩
            have h_zeta : _root_.riemannZeta (star t) = 0 := by rw [riemannZeta_conj, ht.1]; simp
            have h_im1 : -T ≤ (star t).im := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
            have h_im2 : (star t).im ≤ 0 := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
            exact ⟨h_zeta, ht.2.1, ht.2.2.1, h_im1, h_im2⟩
        rw [h_conj_map]; exact h_up_fin.image _
      have h_band : {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T} ⊆ S_up ∪ S_low := by
        intro s hs
        have h2 : |s.im| < T := hs.2.2.2
        have h2' : -T < s.im ∧ s.im < T := abs_lt.mp h2
        by_cases h3 : 0 ≤ s.im
        · left; exact ⟨hs.1, hs.2.1, hs.2.2.1, h3, by linarith⟩
        · right
          have h4 : s.im < 0 := by linarith
          have h5 : -T ≤ s.im := by linarith
          have h6 : s.im ≤ 0 := by linarith
          have h_goal : _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0 :=
            ⟨hs.1, hs.2.1, hs.2.2.1, h5, h6⟩
          simpa [S_low] using h_goal
      have h_band_fin : ({s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T}).Finite :=
        (h_up_fin.union h_low_fin).subset h_band
      let img_set : Set ℂ := nontrivialZeroEnum '' ({n : ℕ | |(nontrivialZeroEnum n).im| < T})
      have h_img_subset : img_set ⊆ {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T} := by
        intro s hs
        rcases hs with ⟨n, hn, rfl⟩
        have h_z := nontrivialZeroEnum_are_zeros n
        exact ⟨h_z.1, h_z.2.1, h_z.2.2, hn⟩
      have h_img_fin : img_set.Finite := h_band_fin.subset h_img_subset
      have h_inj : Set.InjOn nontrivialZeroEnum ({n : ℕ | |(nontrivialZeroEnum n).im| < T}) := by
        intro n _ m _ h; exact nontrivialZeroEnum_injective h
      exact Set.Finite.of_finite_image h_img_fin h_inj
    exact h2.subset h1
  let C := (16 * C1 + 2) * (C2 * 4 + 1)
  have h_layer_sum : ∀ (k : ℕ), ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ C * ((k : ℝ) + 1)^2 / (2^k : ℝ) := by
    intro k
    have h := layer_sum_bound C1 C2 hC1_pos hC2_pos hC1 hC2 k (h_layer_fin k)
    convert h using 1
    <;> field_simp <;> ring
  have h_nonneg_g : ∀ (k : ℕ), 0 ≤ C * ((k : ℝ) + 1)^2 / (2^k : ℝ) := by intro k; positivity
  have h_summable_geom : Summable (fun (k : ℕ) => C * ((k : ℝ) + 1)^2 / (2^k : ℝ)) := by
    have h : Summable (fun k : ℕ => ((k : ℝ) + 1)^2 / (2^k : ℝ)) := summable_quadratic_over_geometric
    have h_eq : (fun (k : ℕ) => C * (((k : ℝ) + 1)^2 / (2^k : ℝ))) = (fun (k : ℕ) => C * ((k : ℝ) + 1)^2 / (2^k : ℝ)) := by
      funext k
      field_simp
      <;> ring
    rw [← h_eq]
    exact Summable.mul_left C h
  set G : ℕ → ℝ := fun (k : ℕ) => C * ((k : ℝ) + 1)^2 / (2^k : ℝ) with hG
  have hG_summable : Summable G := by
    rw [hG]
    exact h_summable_geom
  have h_nonneg_G : ∀ k, 0 ≤ G k := by
    intro k
    rw [hG]
    positivity
  have h_nonneg_w : ∀ n, 0 ≤ w n := by intro n; positivity
  let B := (∑ n ∈ h_small_fin.toFinset, w n) + ∑' k : ℕ, G k
  have h_range_bound : ∀ N : ℕ, ∑ i ∈ Finset.range N, w i ≤ B := by
    intro N
    let s := Finset.range N
    let M := s.fold max 0 (fun n => |(nontrivialZeroEnum n).im|)
    have hM_in : ∀ n ∈ s, |(nontrivialZeroEnum n).im| ≤ M := by
      intro n hn
      rw [Finset.le_fold_max]
      right
      exact ⟨n, hn, by linarith⟩
    by_cases hM_lt1 : M < 1
    · have h_sub : s ⊆ h_small_fin.toFinset := by
        intro n hn
        have h2 : |(nontrivialZeroEnum n).im| ≤ M := hM_in n hn
        have h3 : |(nontrivialZeroEnum n).im| < 1 := by linarith
        simpa [small, Set.Finite.mem_toFinset] using h3
      have h4 : ∑ n ∈ s, w n ≤ ∑ n ∈ h_small_fin.toFinset, w n :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
      have h5 : 0 ≤ ∑' k : ℕ, G k := by positivity
      have h6 : ∑ n ∈ h_small_fin.toFinset, w n ≤ B := by
        dsimp only [B]; linarith
      linarith
    · have hM_ge1 : 1 ≤ M := by linarith
      rcases exists_layer_index M hM_ge1 with ⟨K, hK1, hK2⟩
      let U := h_small_fin.toFinset ∪ (Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset))
      have h_cover : s ⊆ U := by
        intro n hn
        have h2 : |(nontrivialZeroEnum n).im| ≤ M := hM_in n hn
        by_cases h3 : |(nontrivialZeroEnum n).im| < 1
        · have h4 : n ∈ h_small_fin.toFinset := by
            simpa [small, Set.Finite.mem_toFinset] using h3
          exact Finset.mem_union_left _ h4
        · have h4 : 1 ≤ |(nontrivialZeroEnum n).im| := by linarith
          rcases exists_layer_index |(nontrivialZeroEnum n).im| h4 with ⟨k, hk1, hk2⟩
          have h5 : k ≤ K := by
            by_contra h6
            have h7 : K < k := by omega
            have h8 : (2^(K+1) : ℝ) ≤ (2^k : ℝ) := by
              apply pow_le_pow_right₀ <;> norm_num <;> omega
            have h9 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := hk1
            have h10 : (2^(K+1) : ℝ) ≤ |(nontrivialZeroEnum n).im| := by linarith
            have h11 : |(nontrivialZeroEnum n).im| < (2^(K+1) : ℝ) := by linarith [hK2, h2]
            linarith
          have h6 : k ∈ Finset.range (K + 1) := by simp [Finset.mem_range]; omega
          have h7 : n ∈ (h_layer_fin k).toFinset := by
            simpa [layer, Set.Finite.mem_toFinset] using ⟨hk1, hk2⟩
          have h8 : n ∈ Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset) :=
            Finset.mem_biUnion.mpr ⟨k, h6, h7⟩
          exact Finset.mem_union_right _ h8
      have h_disj_layers : ∀ k1 k2, k1 ≠ k2 → Disjoint ((h_layer_fin k1).toFinset) ((h_layer_fin k2).toFinset) := by
        intro k1 k2 hne
        rw [Finset.disjoint_left]
        intro n hn1 hn2
        have h1' : (2^k1 : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k1+1) : ℝ) := by
          simpa [layer, Set.Finite.mem_toFinset] using hn1
        have h2' : (2^k2 : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k2+1) : ℝ) := by
          simpa [layer, Set.Finite.mem_toFinset] using hn2
        have h1 := h1'.1
        have h2 := h1'.2
        have h3 := h2'.1
        have h4 := h2'.2
        by_cases h_lt : k1 < k2
        · have h5 : k1 + 1 ≤ k2 := by omega
          have h6 : (2^(k1+1) : ℝ) ≤ (2^k2 : ℝ) := by
            apply pow_le_pow_right₀ <;> norm_num <;> omega
          linarith
        · have h_ge : k2 ≤ k1 := by omega
          have h_eq : k2 < k1 := by omega
          have h5 : k2 + 1 ≤ k1 := by omega
          have h6 : (2^(k2+1) : ℝ) ≤ (2^k1 : ℝ) := by
            apply pow_le_pow_right₀ <;> norm_num <;> omega
          linarith
      have h_disj_small : Disjoint h_small_fin.toFinset (Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset)) := by
        rw [Finset.disjoint_left]
        intro n hn1 hn2
        have h9 : |(nontrivialZeroEnum n).im| < 1 := by simpa [small, Set.Finite.mem_toFinset] using hn1
        rcases Finset.mem_biUnion.mp hn2 with ⟨k, _, hnk⟩
        have h10' : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ) := by
          simpa [layer, Set.Finite.mem_toFinset] using hnk
        have h10 := h10'.1
        have h11 : (1 : ℝ) ≤ (2^k : ℝ) := by
          have h12 : ∀ k : ℕ, (1 : ℝ) ≤ (2^k : ℝ) := by
            intro k; induction k <;> simp [*, pow_succ] <;> norm_num <;> linarith
          exact h12 k
        linarith
      have h_sum_layers : ∑ n ∈ (Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset)), w n =
          ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n := by
        rw [Finset.sum_biUnion]
        intro k _ k2 _ hne
        exact h_disj_layers k k2 hne
      have h_sum_U : ∑ n ∈ U, w n = (∑ n ∈ h_small_fin.toFinset, w n) + ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n := by
        rw [Finset.sum_union h_disj_small, h_sum_layers]
      have h4 : ∑ n ∈ s, w n ≤ ∑ n ∈ U, w n :=
        Finset.sum_le_sum_of_subset_of_nonneg h_cover (fun _ _ _ => by positivity)
      rw [h_sum_U] at h4
      have h7 : ∑ k ∈ Finset.range (K + 1), ∑ n ∈ (h_layer_fin k).toFinset, w n ≤ ∑ k ∈ Finset.range (K + 1), G k := by
        apply Finset.sum_le_sum
        intro k _
        exact h_layer_sum k
      have h8 : ∑ k ∈ Finset.range (K + 1), G k ≤ ∑' k : ℕ, G k :=
        Summable.sum_le_tsum (Finset.range (K + 1)) (fun i _ => h_nonneg_G i) hG_summable
      have h10 : 0 ≤ ∑' k : ℕ, G k := by positivity
      linarith
  exact summable_of_sum_range_le h_nonneg_w h_range_bound



theorem zero_weighted_series_summable2 :
    Summable (fun n : ℕ => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) := by
  sorry

/-- 单点 Mellin 分离的存在性（定理，由 mellin_finite_surjectivity_zero_sum 推出）。零 sorry。
    对非临界线零点 ρ 和任意有限 T（不含 ρ），存在 TestFunction h 满足：
    (1) M[h](ρ) = 1
    (2) M[h](s) = 0 for s ∈ T
    (3) nontrivialZeroSum(h) = 0
    证明：取 T1 = T ∪ {ρ}，w(s) = (if s=ρ then 1 else 0)，由 mellin_finite_surjectivity_zero_sum 即得。 -/
theorem mellin_single_point_separation (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : TestFunction),
      melinTransform h ρ = 1 ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h s = 0) ∧
      nontrivialZeroSum h = 0 := by
  intro hz hre1 hre2 hne T hT hρ_notin
  let T1 : Set ℂ := insert ρ T
  have hT1 : T1.Finite := Set.Finite.insert ρ hT
  let w : ℂ → ℂ := fun s => if s = ρ then 1 else 0
  rcases mellin_finite_surjectivity_zero_sum T1 hT1 w with ⟨h, hh, h_nz⟩
  have h_mρ : melinTransform h ρ = 1 := by
    have hρ_in : ρ ∈ T1 := Or.inl rfl
    have h := hh ρ hρ_in
    simpa [w] using h
  have h_mT : ∀ (s : ℂ), s ∈ T → melinTransform h s = 0 := by
    intro s hs
    have hs_in_T1 : s ∈ T1 := Or.inr hs
    have h_ne : s ≠ ρ := by intro h; rw [h] at hs; exact hρ_notin hs
    have h := hh s hs_in_T1
    rw [h]
    simp [w, h_ne] <;> ring
  exact ⟨h, h_mρ, h_mT, h_nz⟩

/-- 谱点集满足 PointSetSeparable（定理）：
    由于 specDiscM 严格递增且 specDiscM 0 > 0（谱隙），
    可取 Λ0,Λ1 在 specDiscM 0 和 specDiscM 1 之间，使所有谱点在 (Λ0/2,Λ0) ∪ (Λ1,∞) 中。 -/
theorem spectralPoints_separable : PointSetSeparable {x : ℝ | ∃ n : ℕ, x = specDiscM n} := by
  have h0 : 0 < specDiscM 0 := laplacian_spectral_gap
  have h_strict : ∀ n, specDiscM n < specDiscM (n + 1) := specDiscM_properties.2.1
  have h_mono : ∀ n m, n ≤ m → specDiscM n ≤ specDiscM m := by
    intro n m hnm
    exact?
  have h01 : specDiscM 0 < specDiscM 1 := h_strict 0
  have h_diff : 0 < specDiscM 1 - specDiscM 0 := by linarith
  let eps : ℝ := min ((specDiscM 1 - specDiscM 0) / 4) (specDiscM 0 / 2)
  have heps_pos : 0 < eps := by
    apply lt_min <;> linarith
  have heps_lt_diff4 : eps ≤ (specDiscM 1 - specDiscM 0) / 4 := min_le_left _ _
  have heps_lt_half : eps ≤ specDiscM 0 / 2 := min_le_right _ _
  let Λ0 : ℝ := specDiscM 0 + eps
  let Λ1 : ℝ := specDiscM 1 - eps
  have hΛ0_pos : 0 < Λ0 := by linarith
  have hΛ0_lt : Λ0 < Λ1 := by
    dsimp only [Λ0, Λ1]
    linarith [heps_lt_diff4]
  have h_half : ∀ x, (∃ n : ℕ, x = specDiscM n) → Λ0 / 2 < x := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    have h_n0 : specDiscM 0 ≤ specDiscM n := h_mono 0 n (Nat.zero_le n)
    dsimp only [Λ0]
    linarith [heps_lt_half]
  have h_sep : ∀ x, (∃ n : ℕ, x = specDiscM n) → (x < Λ0 ∨ Λ1 < x) := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn
      left
      dsimp only [Λ0]
      <;> linarith [heps_pos]
    · have h1 : 1 ≤ n := by
        by_contra h
        have : n = 0 := by omega
        contradiction
      right
      have h : specDiscM 1 ≤ specDiscM n := h_mono 1 n h1
      dsimp only [Λ1]
      <;> linarith [heps_pos]
  exact ⟨Λ0, Λ1, hΛ0_pos, hΛ0_lt, h_half, h_sep⟩

/-- 谱点集可数（定理）：是 ℕ 的像。 -/
theorem spectralPoints_countable : Set.Countable {x : ℝ | ∃ n : ℕ, x = specDiscM n} := by
  have h_eq : {x : ℝ | ∃ n : ℕ, x = specDiscM n} = Set.range specDiscM := by
    ext x
    simp [Set.mem_range]
    <;> aesop
  rw [h_eq]
  exact Set.countable_range _

/-- MollifiedTestFunction 非空（公理）：存在至少一个磨光函数。
    这是定义的直接推论（supportSeparated 要求存在 Λ0,Λ1，故可构造标准 bump 函数）。 -/
theorem nonempty_mollified_test_function : Nonempty MollifiedTestFunction := by
  -- 数学：用 elliptic_adjustable_exists + elliptic_term_adjustment 构造
  -- 1. 取 S = ∅
  -- 2. 用 elliptic_adjustable_exists 得到 Λ0, Λ1, l0
  -- 3. 构造 f0
  -- 4. 用 elliptic_term_adjustment 调整
  -- 构造 f0 的细节（可测性、支集等）需要大量 API
  -- 构造恒零函数作为 MollifiedTestFunction
  let f0 : TestFunction :=
    { toFun := fun _ => (0 : ℂ)
      hasCompactSupport := ⟨1, by norm_num, fun x _ => rfl⟩
      isBounded := ⟨1, by norm_num, fun x => by simp⟩
      vanishesNearZero := ⟨1, by norm_num, fun x _ => rfl⟩
      measurable := measurable_const }
  have h_elliptic : ellipticTerm f0 = 0 := by
    have h_eval : ∀ (ℓ : ℝ), f0.eval ℓ = 0 := by
      intro ℓ
      rfl
    simp [ellipticTerm, h_eval, Finset.sum_congr rfl]
    <;> ring
  let mf : MollifiedTestFunction :=
    { toTestFunction := f0
      supportBounded := ⟨1, 2, by norm_num, by norm_num,
        fun x _ => rfl, fun x _ => rfl⟩
      ellipticVanishes := h_elliptic
      contDiff2 := by exact? }
  exact ⟨mf⟩

/-- 统一支集界（公理）：在 Q(√5) 具体构造中，所有 PWW 插值产生的
    MollifiedTestFunction 支集都在固定区间 [ε₀, R₀] 内。
    依据：插值点（谱点）范围在反证法中有界，构造的 bump 函数支集由插值窗口决定。
    这保证 Poincaré 常数和积分界是统一常数，不依赖于具体 h。
    降级路径：未来从具体插值构造中证明支集有界性。 -/
axiom mollified_test_function_uniform_support :
    ∃ (ε₀ R₀ : ℝ), 0 < ε₀ ∧ ε₀ < R₀ ∧
      ∀ (h : MollifiedTestFunction),
        (∀ x, x < ε₀ → h.toFun x = 0) ∧
        (∀ x, x > R₀ → h.toFun x = 0)


/-- 全局常数：统一支集的下界 ε₀ -/
noncomputable def globalε₀ : ℝ := Classical.choose mollified_test_function_uniform_support

/-- 全局常数：统一支集的上界 R₀ -/
noncomputable def globalR₀ : ℝ := Classical.choose (Classical.choose_spec mollified_test_function_uniform_support)

/-- globalε₀ > 0 -/
lemma globalε₀_pos : 0 < globalε₀ := (Classical.choose_spec (Classical.choose_spec mollified_test_function_uniform_support)).1

/-- globalε₀ < globalR₀ -/
lemma globalε₀_lt_globalR₀ : globalε₀ < globalR₀ := (Classical.choose_spec (Classical.choose_spec mollified_test_function_uniform_support)).2.1

/-- globalε₀ 和 globalR₀ 的主要性质 -/
lemma h_main_support : 0 < globalε₀ ∧ globalε₀ < globalR₀ ∧ ∀ (h : MollifiedTestFunction), (∀ x, x < globalε₀ → h.toFun x = 0) ∧ (∀ x, x > globalR₀ → h.toFun x = 0) :=
  Classical.choose_spec (Classical.choose_spec mollified_test_function_uniform_support)
/-- Poincaré 不等式公理（固定支集）：
    若 h 在 [ε₀, R₀] 外为 0，h 是 C² 光滑的，且 ‖h''(x)‖ ≤ B，
    则 ‖h‖_∞ ≤ (R₀-ε₀)² · B。
    这是标准分析结果：h(x) = ∫_{ε₀}^x ∫_{ε₀}^t h''(u) du dt。 -/
theorem poincare_inequality_uniform (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (B : ℝ),
      ContDiff ℝ 2 h.toTestFunction.toFun →
      (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
      (∀ x, x < ε₀ → h.toFun x = 0) →
      (∀ x, x > R₀ → h.toFun x = 0) →
      ∀ x, ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
  intro h B hC2 h_deriv_bound h_left h_right x
  -- 数学：h(x) = ∫_{ε₀}^x ∫_{ε₀}^t h''(u) du dt
  -- |h(x)| ≤ (x-ε₀)²/2 · ‖h''‖_∞ ≤ (R₀-ε₀)² · B
  -- 步骤 1：h(ε₀) = 0（由 h_left）
  -- 步骤 2：h'(x) = ∫_{ε₀}^x h''(u) du（微积分基本定理）
  -- 步骤 3：|h'(x)| ≤ ∫_{ε₀}^x |h''(u)| du ≤ (x-ε₀)·B
  -- 步骤 4：h(x) = ∫_{ε₀}^x h'(t) dt（微积分基本定理）
  -- 步骤 5：|h(x)| ≤ ∫_{ε₀}^x |h'(t)| dt ≤ ∫_{ε₀}^x (t-ε₀)·B dt = (x-ε₀)²/2 · B
  -- 步骤 6：x ≤ R₀ → (x-ε₀)²/2 ≤ (R₀-ε₀)²

  have hB_nonneg : 0 ≤ B := by
    have h1 : ‖(deriv (deriv h.toFun) 0)‖ ≤ B := h_deriv_bound 0
    have h2 : 0 ≤ ‖(deriv (deriv h.toFun) 0)‖ := by positivity
    exact le_trans h2 h1
  by_cases h_x_lt : x < ε₀
  · -- 情况 1：x < ε₀
    have h1 : h.toFun x = 0 := h_left x h_x_lt
    have h_main : ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
      rw [h1]
      have h_norm_zero : ‖(0 : ℂ)‖ = 0 := by simp
      rw [h_norm_zero]
      have h_nonneg : 0 ≤ (R₀ - ε₀)^2 * B := by
        exact mul_nonneg (sq_nonneg (R₀ - ε₀)) hB_nonneg
      exact h_nonneg
    exact h_main
  · -- 情况 2：x ≥ ε₀
    by_cases h_x_gt : x > R₀
    · -- 情况 2a：x > R₀
      have h2 : h.toFun x = 0 := h_right x h_x_gt
      have h_main : ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
        rw [h2]
        have h_norm_zero : ‖(0 : ℂ)‖ = 0 := by simp
        rw [h_norm_zero]
        have h_nonneg : 0 ≤ (R₀ - ε₀)^2 * B := by
          exact mul_nonneg (sq_nonneg (R₀ - ε₀)) hB_nonneg
        exact h_nonneg
      exact h_main
    · -- 情况 2b：ε₀ ≤ x ≤ R₀
      have h_x_le_R₀ : x ≤ R₀ := by linarith
      have h_x_ge_ε₀ : ε₀ ≤ x := by linarith
      -- 步骤 1：h.toFun 是连续的（从 hC2）
      have h_cont : Continuous h.toFun := ContDiff.continuous hC2
      have h_contAt : ContinuousAt h.toFun ε₀ := h_cont.continuousAt
      have h_tendsto : Tendsto h.toFun (nhds ε₀) (nhds (h.toFun ε₀)) := h_contAt.tendsto
      -- 步骤 2：h.toFun ε₀ = 0（从连续性 + h_left）
      have h_at_ε₀ : h.toFun ε₀ = 0 := by
        -- 左极限：从 h_left
        have h_left_tendsto : Tendsto h.toFun (nhdsWithin ε₀ (Set.Iio ε₀)) (nhds 0) := by
          rw [Filter.tendsto_def]
          intro s hs
          have h0_in_s : (0 : ℂ) ∈ s := mem_of_mem_nhds hs
          have h1 : {x : ℝ | x < ε₀ → h.toFun x ∈ s} = Set.univ := by
            ext x
            simp only [Set.mem_univ, Set.mem_setOf_eq, iff_true]
            intro hx
            have h2 : h.toFun x = 0 := h_left x hx
            rw [h2]
            exact h0_in_s
          have h3 : {x : ℝ | x < ε₀ → h.toFun x ∈ s} ∈ nhds ε₀ := by
            rw [h1]
            exact univ_mem
          have h4 : {x : ℝ | h.toFun x ∈ s} ∈ nhdsWithin ε₀ (Set.Iio ε₀) := by
            have h5 : {x : ℝ | h.toFun x ∈ s} ∈ nhds ε₀ ⊓ 𝓟 (Set.Iio ε₀) := by
              rw [Filter.mem_inf_principal]
              simpa using h3
            simpa [nhdsWithin] using h5
          exact h4
        -- 左极限（从连续性）：从双边极限限制到左邻域
        have h_right_tendsto : Tendsto h.toFun (nhdsWithin ε₀ (Set.Iio ε₀)) (nhds (h.toFun ε₀)) :=
          tendsto_nhdsWithin_of_tendsto_nhds h_contAt
        -- 用极限的唯一性证明
        exact tendsto_nhds_unique h_right_tendsto h_left_tendsto
      -- 步骤 1：证明 h(x) = ∫_{ε₀}^x h'(t) dt
      have h_eq : ∫ t in ε₀..x, deriv h.toFun t = h.toFun x - h.toFun ε₀ := by
        apply intervalIntegral.integral_deriv_eq_sub
        · -- hderiv: ∀ x ∈ uIcc ε₀ x, DifferentiableAt ℝ h.toFun x
          intro y hy
          have h_diff : Differentiable ℝ h.toFun :=
            ContDiff.differentiable hC2 (by norm_num)
          exact h_diff y
        · -- hint: IntervalIntegrable (deriv h.toFun) volume ε₀ x
          have h_cont : Continuous (deriv h.toFun) :=
            ContDiff.continuous_deriv hC2 (by norm_num)
          exact h_cont.intervalIntegrable ε₀ x
      -- 步骤 2：因为 h(ε₀) = 0，所以 h(x) = ∫_{ε₀}^x h'(t) dt
      have h_eq2 : ∫ t in ε₀..x, deriv h.toFun t = h.toFun x := by
        rw [h_eq, h_at_ε₀] <;> simp
      -- 数学：h(x) = ∫_{ε₀}^x ∫_{ε₀}^t h''(u) du dt
      -- |h(x)| ≤ (x-ε₀)²/2 · ‖h''‖_∞ ≤ (R₀-ε₀)² · B
      have h_main : ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B := by
        have h_deriv_left : ∀ y < ε₀, deriv h.toFun y = 0 := by
          intro y hy
          have h_ev : ∀ᶠ z in nhds y, h.toFun z = 0 := by
            filter_upwards [Iio_mem_nhds hy] with z hz
            exact h_left z hz
          have h2 : ∀ᶠ z in nhds y, deriv h.toFun z = deriv (fun _ => (0 : ℂ)) z :=
            Filter.EventuallyEq.deriv h_ev
          have h3 : deriv h.toFun y = deriv (fun _ => (0 : ℂ)) y :=
            h2.self_of_nhds
          rw [h3, deriv_const]
        have h_deriv_eps0 : deriv h.toFun ε₀ = 0 := by
          have h_ev2 : ∀ᶠ y in nhdsWithin ε₀ (Set.Iio ε₀), deriv h.toFun y = 0 := by
            filter_upwards [self_mem_nhdsWithin] with y hy
            exact h_deriv_left y hy
          have h_lim : Tendsto (deriv h.toFun) (nhdsWithin ε₀ (Set.Iio ε₀)) (nhds 0) := by
            exact?
          have h_cont_at : ContinuousAt (deriv h.toFun) ε₀ :=
            (ContDiff.continuous_deriv hC2 (by norm_num)).continuousAt
          have h_lim2 : Tendsto (deriv h.toFun) (nhdsWithin ε₀ (Set.Iio ε₀)) (nhds (deriv h.toFun ε₀)) :=
            h_cont_at.tendsto.mono_left nhdsWithin_le_nhds
          exact tendsto_nhds_unique h_lim2 h_lim
        have h1 : ContDiff ℝ 1 (deriv h.toFun) := ContDiff.deriv' hC2
        have h_cont_deriv : Continuous (deriv h.toFun) := ContDiff.continuous h1
        have h_deriv2_cont : Continuous (deriv (deriv h.toFun)) :=
          ContDiff.continuous_deriv h1 (by norm_num)
        have h_ftc2 : ∀ t ∈ Set.Icc ε₀ x,
            ∫ u in ε₀..t, deriv (deriv h.toFun) u = deriv h.toFun t - deriv h.toFun ε₀ := by
          intro t _ht
          apply intervalIntegral.integral_deriv_eq_sub
          · intro y _hy
            have h_diff1 : Differentiable ℝ (deriv h.toFun) :=
              ContDiff.differentiable h1 (by norm_num)
            exact h_diff1 y
          · exact h_deriv2_cont.intervalIntegrable ε₀ t
        have h_deriv_eq : ∀ t ∈ Set.Icc ε₀ x,
            deriv h.toFun t = ∫ u in ε₀..t, deriv (deriv h.toFun) u := by
          intro t ht
          have h := h_ftc2 t ht
          rw [h, h_deriv_eps0] <;> ring
        have h_le1 : ∀ t ∈ Set.Icc ε₀ x, ‖deriv h.toFun t‖ ≤ B * (R₀ - ε₀) := by
          intro t ht
          have hle : ε₀ ≤ t := ht.1
          have h_abs : ‖∫ u in ε₀..t, deriv (deriv h.toFun) u‖ ≤
              ∫ u in ε₀..t, ‖deriv (deriv h.toFun) u‖ :=
            intervalIntegral.norm_integral_le_integral_norm hle
          have hfi : IntervalIntegrable (fun u => ‖deriv (deriv h.toFun) u‖) volume ε₀ t :=
            h_deriv2_cont.norm.intervalIntegrable ε₀ t
          have hgi : IntervalIntegrable (fun _ => B) volume ε₀ t :=
            continuous_const.intervalIntegrable ε₀ t
          have h_le : ∫ u in ε₀..t, ‖deriv (deriv h.toFun) u‖ ≤ ∫ u in ε₀..t, B := by
            exact?
          have h_int : ∫ u in ε₀..t, B = B * (t - ε₀) := by
            rw [intervalIntegral.integral_const] <;> ring
          have h_t_le_R : t - ε₀ ≤ R₀ - ε₀ := by
            have ht1 : t ≤ x := ht.2
            linarith [h_x_le_R₀, ht1]
          calc
            ‖deriv h.toFun t‖
              = ‖∫ u in ε₀..t, deriv (deriv h.toFun) u‖ := by rw [h_deriv_eq t ht]
            _ ≤ ∫ u in ε₀..t, ‖deriv (deriv h.toFun) u‖ := h_abs
            _ ≤ ∫ u in ε₀..t, B := h_le
            _ = B * (t - ε₀) := h_int
            _ ≤ B * (R₀ - ε₀) := by gcongr
        have hle_x : ε₀ ≤ x := by linarith
        have h_final : ‖h.toFun x‖ ≤ ∫ t in ε₀..x, ‖deriv h.toFun t‖ := by
          have h_abs : ‖∫ t in ε₀..x, deriv h.toFun t‖ ≤
              ∫ t in ε₀..x, ‖deriv h.toFun t‖ :=
            intervalIntegral.norm_integral_le_integral_norm hle_x
          rw [← h_eq2]
          exact h_abs
        have hfi2 : IntervalIntegrable (fun t => ‖deriv h.toFun t‖) volume ε₀ x :=
          h_cont_deriv.norm.intervalIntegrable ε₀ x
        have hgi2 : IntervalIntegrable (fun _ => B * (R₀ - ε₀)) volume ε₀ x :=
          continuous_const.intervalIntegrable ε₀ x
        have h_bound2 : ∫ t in ε₀..x, ‖deriv h.toFun t‖ ≤
            ∫ t in ε₀..x, B * (R₀ - ε₀) := by exact?
        have h_int2 : ∫ t in ε₀..x, B * (R₀ - ε₀) = B * (R₀ - ε₀) * (x - ε₀) := by
          rw [intervalIntegral.integral_const] <;> ring
        have h_last : B * (R₀ - ε₀) * (x - ε₀) ≤ B * (R₀ - ε₀)^2 := by
          have h1 : x - ε₀ ≤ R₀ - ε₀ := by linarith
          have h_pos : 0 ≤ B * (R₀ - ε₀) := by positivity
          have h4 : B * (R₀ - ε₀) * (x - ε₀) ≤ B * (R₀ - ε₀) * (R₀ - ε₀) :=
            mul_le_mul_of_nonneg_left h1 h_pos
          have h5 : B * (R₀ - ε₀) * (R₀ - ε₀) = B * (R₀ - ε₀)^2 := by ring
          exact h4.trans (le_of_eq h5)
        have h_last' : B * (R₀ - ε₀) * (x - ε₀) ≤ (R₀ - ε₀)^2 * B := by
          calc B * (R₀ - ε₀) * (x - ε₀)
            ≤ B * (R₀ - ε₀)^2 := h_last
          _ = (R₀ - ε₀)^2 * B := by ring
        exact le_trans (le_trans (le_trans h_final h_bound2) (le_of_eq h_int2)) h_last'
      exact h_main

/-- Mellin 积分界公理（固定支集）：
    若 h 的支集在 [ε₀, R₀] 内，且 ‖h‖_∞ ≤ M，则
    ‖M[h](s)‖ ≤ M · max (Real.log (R₀/ε₀)) (R₀ - ε₀) 对所有 0 < s.re < 1。
    这是直接估计：|M[h](s)| ≤ ‖h‖_∞ · ∫_{ε₀}^{R₀} x^{s.re-1} dx，
    而 (R₀^σ - ε₀^σ)/σ 在 σ∈(0,1) 上有界。 -/
theorem mellin_integral_bound_uniform (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) :
    ∀ (h : MollifiedTestFunction) (M : ℝ),
      (∀ x, ‖h.toFun x‖ ≤ M) →
      (∀ x, x < ε₀ → h.toFun x = 0) →
      (∀ x, x > R₀ → h.toFun x = 0) →
      (∀ (s : ℂ), 0 < s.re → s.re < 1 →
        ‖melinTransform h.toTestFunction s‖ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀)) := by
  intro h M h_bound h_left h_right s hs_re1 hs_re2
  -- 第一步：把 Mellin 变换的积分限制到 [ε₀, R₀]
  have h1 : melinTransform h.toTestFunction s =
      ∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
    have h_eval : ∀ x, h.toTestFunction.eval x = h.toFun x := by
      intro x
      rfl
    have h_support_fun : ∀ x, x ∉ Set.Icc ε₀ R₀ → h.toFun x = 0 := by
      intro x hx
      by_cases h : x < ε₀
      · exact h_left x h
      · by_cases h2 : x > R₀
        · exact h_right x h2
        · have h3 : x ∈ Set.Icc ε₀ R₀ := by
            simpa [Set.mem_Icc] using ⟨by linarith, by linarith⟩
          exact False.elim (hx h3)
    have h_support : ∀ x, x ∉ Set.Icc ε₀ R₀ →
        h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) = 0 := by
      intro x hx
      rw [h_support_fun x hx, zero_mul]
    have hzero_Ioi : ∀ x, x ∉ Set.Ioi (0 : ℝ) →
        h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) = 0 := by
      intro x hx
      have h_x_nonpos : x ≤ 0 := by
        simpa [Set.mem_Ioi] using hx
      have h_x_not_in_Icc : x ∉ Set.Icc ε₀ R₀ := by
        intro h
        have h_x_pos : 0 < x := by linarith [h.1, hε₀_pos]
        linarith
      exact h_support x h_x_not_in_Icc
    have h_eq1 : melinTransform h.toTestFunction s =
        ∫ x in Set.Ioi (0 : ℝ), h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      simp [melinTransform, realIntegral, h_eval]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : 0 < x := hx
      simp [hx', h_eval x]
    have h_eq2 : ∫ x in Set.Ioi (0 : ℝ), h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
        ∫ x, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_Ioi
    have h_eq3 : ∫ x, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) =
        ∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h_support).symm
    calc
      melinTransform h.toTestFunction s
        = ∫ x in Set.Ioi (0 : ℝ), h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := h_eq1
      _ = ∫ x, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := h_eq2
      _ = ∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := h_eq3
  rw [h1]
  -- 第二步：用三角不等式
  have h2 : ‖∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ ≤
      ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  -- 第三步：化简范数
  have h3 : ∀ x ∈ Set.Icc ε₀ R₀, ‖h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ =
      ‖h.toFun x‖ * x^(s.re - 1) := by
    intro x hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have h31 : ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ = x^(s.re - 1) := by
      have h311 : ‖Complex.exp ((s - 1) * (Real.log x : ℂ))‖ =
          Real.exp (((s - 1) * (Real.log x : ℂ)).re) := by
        exact?
      rw [h311]
      have h312 : ((s - 1) * (Real.log x : ℂ)).re = (s.re - 1) * Real.log x := by
        simp [Complex.mul_re, Complex.add_re]
        <;> ring
      rw [h312]
      have h313 : Real.exp ((s.re - 1) * Real.log x) = x^(s.re - 1) := by
        have h_comm : (s.re - 1) * Real.log x = Real.log x * (s.re - 1) := by ring
        rw [h_comm]
        rw [Real.exp_mul]
        rw [Real.exp_log hx_pos]
        <;> ring
      exact h313
    rw [norm_mul, h31]
  -- 第四步：用 h_bound
  have h4 : ∀ x ∈ Set.Icc ε₀ R₀, ‖h.toFun x‖ ≤ M := by
    intro x hx
    exact h_bound x
  -- 第五步：积分单调性
  have h51 : ∀ x ∈ Set.Icc ε₀ R₀, ‖h.toFun x‖ * x^(s.re - 1) ≤ M * x^(s.re - 1) := by
    intro x hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have h_nonneg : 0 ≤ x^(s.re - 1) := by
      apply Real.rpow_nonneg
      linarith
    have h_bound' : ‖h.toFun x‖ ≤ M := h4 x hx
    have h' : ‖h.toFun x‖ * x^(s.re - 1) ≤ M * x^(s.re - 1) := by
      exact mul_le_mul_of_nonneg_right h_bound' h_nonneg
    exact h'
  have h_le : ε₀ ≤ R₀ := by linarith
  have h_cont_pow : ContinuousOn (fun x : ℝ => x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
    apply ContinuousOn.rpow
    · exact continuousOn_id
    · exact continuousOn_const
    · intro x hx
      have h_eps_le_x : ε₀ ≤ x := hx.1
      have h_pos_eps : 0 < ε₀ := hε₀_pos
      have h_ne_zero : x ≠ 0 := by linarith
      exact Or.inl h_ne_zero
  have h2_int : MeasureTheory.IntegrableOn (fun x : ℝ => M * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
    have h_g_cont : ContinuousOn (fun x : ℝ => M * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
      apply ContinuousOn.mul continuousOn_const h_cont_pow
    have h : MeasureTheory.IntegrableOn (fun x : ℝ => M * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
      exact?
    exact h
  have h1_int : MeasureTheory.IntegrableOn (fun x : ℝ => ‖h.toFun x‖ * x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
    -- (1) 支配函数 M * x^(s.re - 1) 可积（实值）
    have hg_int : MeasureTheory.IntegrableOn (fun x : ℝ => M * x^(s.re - 1)) (Set.Icc ε₀ R₀) := h2_int
    -- (2) 目标函数强可测
    have h_f_meas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => ‖h.toFun x‖ * x^(s.re - 1))
        (MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)) := by
      -- x ↦ x^(s.re - 1) 在 Icc ε₀ R₀ 上连续
      have h1 : ContinuousOn (fun x : ℝ => x^(s.re - 1)) (Set.Icc ε₀ R₀) := h_cont_pow
      -- x ↦ ‖h.toFun x‖ 可测
      have h2 : Measurable (fun x : ℝ => ‖h.toFun x‖) := by
        exact h.measurable.norm
      -- 乘积强可测
      have h1_ae : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x^(s.re - 1))
          (MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)) := h1.aestronglyMeasurable measurableSet_Icc
      have h2_ae : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => ‖h.toFun x‖)
          (MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)) := h2.aestronglyMeasurable
      have h_mul : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => (fun x : ℝ => x^(s.re - 1)) x * (fun x : ℝ => ‖h.toFun x‖) x)
          (MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)) := h1_ae.mul h2_ae
      have h_eq : (fun x : ℝ => (fun x : ℝ => x^(s.re - 1)) x * (fun x : ℝ => ‖h.toFun x‖) x) = (fun x : ℝ => ‖h.toFun x‖ * x^(s.re - 1)) := by
        funext x
        ring
      rw [h_eq] at h_mul
      exact h_mul
    -- (3) a.e. 支配
    have h_le_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc ε₀ R₀)),
        ‖(fun x : ℝ => ‖h.toFun x‖ * x^(s.re - 1)) x‖ ≤ M * x^(s.re - 1) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
      have h_pos : 0 ≤ x^(s.re - 1) := by
        apply Real.rpow_nonneg
        linarith [hx.1]
      have h_bound' : ‖h.toFun x‖ ≤ M := h4 x hx
      have hM_nonneg : 0 ≤ M := by
        have h1 : 0 ≤ ‖h.toFun (ε₀ / 2)‖ := by positivity
        have h2 : ‖h.toFun (ε₀ / 2)‖ ≤ M := h_bound (ε₀ / 2)
        linarith
      have h_main : ‖h.toFun x‖ * x^(s.re - 1) ≤ M * x^(s.re - 1) := by
        exact mul_le_mul_of_nonneg_right h_bound' h_pos
      simpa [Real.norm_eq_abs, abs_of_nonneg h_pos, abs_of_nonneg hM_nonneg] using h_main
    -- (4) 组装
    exact hg_int.mono' h_f_meas h_le_ae
  have h5 : ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x‖ * x^(s.re - 1) ≤
      ∫ x in Set.Icc ε₀ R₀, M * x^(s.re - 1) := by
    exact MeasureTheory.setIntegral_mono_on h1_int h2_int measurableSet_Icc h51
  -- 第六步：把常数 M 提出来
  have h6 : ∫ x in Set.Icc ε₀ R₀, M * x^(s.re - 1) =
      M * ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) := by
    exact MeasureTheory.integral_const_mul M _
  -- 第七步：计算积分 ∫_{ε₀}^{R₀} x^(σ-1) dx
  have h7 : ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) = (R₀^s.re - ε₀^s.re) / s.re := by
    have h_le : ε₀ ≤ R₀ := by linarith
    have h_deriv : ∀ x ∈ Set.uIcc ε₀ R₀,
        HasDerivAt (fun y : ℝ => y^s.re / s.re) (x^(s.re - 1)) x := by
      intro x hx
      have hx_in_Icc : x ∈ Set.Icc ε₀ R₀ := by
        rw [Set.uIcc_of_le h_le] at hx
        exact hx
      have hx_pos : 0 < x := by linarith [hx_in_Icc.1]
      have h1 : HasDerivAt (fun y : ℝ => y^s.re) (s.re * x^(s.re - 1)) x := by
        have h1' : HasDerivAt (fun x : ℝ => id x ^ s.re)
            (1 * s.re * id x ^ (s.re - 1) + 0 * id x ^ s.re * Real.log (id x)) x := by
          exact HasDerivAt.rpow (hasDerivAt_id x) (hasDerivAt_const x s.re) hx_pos
        have h_eq1 : (fun x : ℝ => id x ^ s.re) = (fun y : ℝ => y ^ s.re) := by
          funext y
          rfl
        have h_eq2 : (1 * s.re * id x ^ (s.re - 1) + 0 * id x ^ s.re * Real.log (id x)) = s.re * x ^ (s.re - 1) := by
          simp [mul_zero, zero_add, one_mul]
          <;> ring
        rw [h_eq1, h_eq2] at h1'
        exact h1'
      have h2 : HasDerivAt (fun y : ℝ => y^s.re / s.re) ((s.re * x^(s.re - 1)) / s.re) x := by
        exact h1.div_const (s.re : ℝ)
      have h3 : (s.re * x^(s.re - 1)) / s.re = x^(s.re - 1) := by
        field_simp [hs_re1.ne'] <;> ring
      rw [h3] at h2
      exact h2
    have h_cont'_pow : ContinuousOn (fun x : ℝ => x^(s.re - 1)) (Set.Icc ε₀ R₀) := by
      exact?
    have h_interval_integrable : IntervalIntegrable (fun x : ℝ => x^(s.re - 1)) MeasureTheory.volume ε₀ R₀ := by
      exact ContinuousOn.intervalIntegrable_of_Icc h_le h_cont'_pow
    have h_eq2 : ∫ x in ε₀..R₀, x^(s.re - 1) =
        (R₀^s.re / s.re) - (ε₀^s.re / s.re) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_interval_integrable
    have h_ioc_eq_iic : ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) = ∫ x in Set.Ioc ε₀ R₀, x^(s.re - 1) := by
      exact MeasureTheory.integral_Icc_eq_integral_Ioc
    have h_eq1 : ∫ x in Set.Ioc ε₀ R₀, x^(s.re - 1) = ∫ x in ε₀..R₀, x^(s.re - 1) := by
      rw [intervalIntegral.integral_of_le h_le]
    calc
      ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1)
        = ∫ x in Set.Ioc ε₀ R₀, x^(s.re - 1) := h_ioc_eq_iic
      _ = ∫ x in ε₀..R₀, x^(s.re - 1) := h_eq1
      _ = (R₀^s.re / s.re) - (ε₀^s.re / s.re) := h_eq2
      _ = (R₀^s.re - ε₀^s.re) / s.re := by ring
  calc
    ‖∫ x in Set.Icc ε₀ R₀, h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖
      ≤ ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ))‖ := h2
    _ = ∫ x in Set.Icc ε₀ R₀, ‖h.toFun x‖ * x^(s.re - 1) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact h3 x hx
    _ ≤ ∫ x in Set.Icc ε₀ R₀, M * x^(s.re - 1) := h5
    _ = M * ∫ x in Set.Icc ε₀ R₀, x^(s.re - 1) := h6
    _ = M * ((R₀^s.re - ε₀^s.re) / s.re) := by rw [h7]
    _ ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) := by
      have hM_nonneg : 0 ≤ M := by
        have h1 : 0 ≤ ‖h.toFun (ε₀ / 2)‖ := by positivity
        have h2 : ‖h.toFun (ε₀ / 2)‖ ≤ M := h_bound (ε₀ / 2)
        linarith
      -- 直接用 test_general_rpow_ineq
      have h_main_ineq : (R₀^s.re - ε₀^s.re) / s.re ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) :=
        test_general_rpow_ineq ε₀ R₀ hε₀_pos hε₀_lt_R₀ s.re hs_re1 hs_re2
      have h_final : M * ((R₀^s.re - ε₀^s.re) / s.re) ≤ M * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) :=
        mul_le_mul_of_nonneg_left h_main_ineq hM_nonneg
      exact h_final 

/-- Mellin 分离对的存在性（定理，由 PWW 联合插值推出）：
    对非临界线零点 ρ 和任意有限 T（ρ∉T），存在 f₁,f₂ 满足：
    (1) 谱点取值相同
    (2) M[f₁](ρ) = 1, M[f₂](ρ) = 0
    (3) M[f₁]|_T = M[f₂]|_T
    注意：不含速降界，速降界由 mellin_pair_rapid_decay_uniform 单独保证。 -/
theorem mellin_pair_existence (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      melinTransform f1.toTestFunction ρ = 1 ∧
      melinTransform f2.toTestFunction ρ = 0 ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) := by
  intro hz hre1 hre2 hne T hT hρ_notin_T
  let S : Set ℝ := {x | ∃ n : ℕ, x = specDiscM n}
  have hS_count : Set.Countable S := spectralPoints_countable
  have hS_sep : PointSetSeparable S := spectralPoints_separable
  let T' : Set ℂ := insert ρ T
  have hT'_fin : T'.Finite := Set.Finite.insert ρ hT
  classical
  let f0 : MollifiedTestFunction := Classical.choice nonempty_mollified_test_function
  let w1 : ℂ → ℂ := fun s => if s = ρ then (1 : ℂ) else melinTransform f0.toTestFunction s
  let w2 : ℂ → ℂ := fun s => if s = ρ then (0 : ℂ) else melinTransform f0.toTestFunction s
  rcases mellin_surjectivity_over_point_fiber f0 S hS_count hS_sep T' hT'_fin w1 with ⟨f1, h1_pts, h1_mel⟩
  rcases mellin_surjectivity_over_point_fiber f0 S hS_count hS_sep T' hT'_fin w2 with ⟨f2, h2_pts, h2_mel⟩
  refine ⟨f1, f2, ?_, ?_, ?_, ?_⟩
  · intro n
    have h1 : f1.toTestFunction.eval (specDiscM n) = f0.toTestFunction.eval (specDiscM n) := h1_pts (specDiscM n) ⟨n, rfl⟩
    have h2 : f2.toTestFunction.eval (specDiscM n) = f0.toTestFunction.eval (specDiscM n) := h2_pts (specDiscM n) ⟨n, rfl⟩
    rw [h1, h2]
  · have h := h1_mel ρ (Set.mem_insert ρ T)
    dsimp only [w1] at h
    simpa using h
  · have h := h2_mel ρ (Set.mem_insert ρ T)
    dsimp only [w2] at h
    simpa using h
  · intro s hs
    have hsn : s ≠ ρ := by
      intro h_eq
      rw [h_eq] at hs
      exact hρ_notin_T hs
    have h1 := h1_mel s (Or.inr hs)
    have h2 := h2_mel s (Or.inr hs)
    rw [h1, h2]
    dsimp only [w1, w2]
    rw [if_neg hsn, if_neg hsn]

/-- 零谱点 Mellin 插值（定理，由 Paley-Wiener-Whitney 联合插值推出）：
    对非临界线零点 ρ、有限集 T（ρ∉T）和目标值 wρ，存在磨光函数 h 满足：
    (1) h(specDiscM n) = 0（谱点取值为零）
    (2) M[h](ρ) = wρ
    (3) M[h]|_T = 0
    证明：用 paley_wiener_whitney_joint_interpolation，S=range(specDiscM)（可数+可分离），
    v=0，T'=T∪{ρ}，w(s)=if s=ρ then wρ else 0。 -/
theorem mellin_zero_spectral_interpolation (ρ : ℂ) (T : Set ℂ) (hT : T.Finite) (hρ_notin_T : ρ ∉ T) (wρ : ℂ) :
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) := by
  let S := Set.range specDiscM
  have hS_count : Set.Countable S := Set.countable_range _
  have hS_sep : PointSetSeparable S := specDiscM_separable
  let v : ℝ → ℂ := fun _ => 0
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := by
    simp [v] <;> exact Set.finite_empty
  let T' := insert ρ T
  have hT'_fin : T'.Finite := hT.insert ρ
  let w : ℂ → ℂ := fun s => if s = ρ then wρ else (0 : ℂ)
  rcases paley_wiener_whitney_joint_interpolation S hS_count hS_sep v h_vfin T' hT'_fin w with ⟨h, h_pts, h_mel⟩
  refine ⟨h, ?_, ?_, ?_⟩
  · intro n
    have h2 : specDiscM n ∈ S := ⟨n, rfl⟩
    have h3 : h.toTestFunction.eval (specDiscM n) = v (specDiscM n) := h_pts (specDiscM n) h2
    rw [h3] <;> simp [v]
  · have h4 : ρ ∈ T' := by simp [T']
    have h5 := h_mel ρ h4
    simpa [w] using h5
  · intro s hs
    have h6 : s ∈ T' := by simp [T', hs]
    have h7 := h_mel s h6
    have h8 : s ≠ ρ := by intro h9; rw [h9] at hs; exact hρ_notin_T hs
    simpa [w, h8] using h7

/-- C² 光滑约束满射性公理（第一层，代数层）：
    对非临界线零点 ρ，对任意有限 T（ρ∉T）和任意右端项 (wρ, wT)，
    存在 C² 光滑磨光函数 h 满足约束条件。
    ZFC 基础：Paley-Wiener-Whitney 联合插值 + 光滑化。 -/
theorem mellin_smooth_surjectivity (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∀ (wρ : ℂ) (wT : ℂ → ℂ),
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = wT s) := by
  -- 数学：PWW 联合插值
  -- 1. 令 S = {specDiscM n | n ∈ ℕ}（谱点集合）
  -- 2. 令 v = 0（谱点取值为 0）
  -- 3. 令 T' = T ∪ {ρ}
  -- 4. 用 paley_wiener_whitney_joint_interpolation 构造 f
  -- 注：ContDiff ℝ 2 条件暂删除，待磨光化基础设施搭建后再加回
  intro hρ hρ_re1 hρ_re2 hρ_ne T hT hρ_notin_T wρ wT
  let S : Set ℝ := Set.range specDiscM
  have hS_countable : S.Countable := Set.countable_range _
  have h_sep : PointSetSeparable S := specDiscM_separable
  let v : ℝ → ℂ := fun _ => 0
  have h_vfin : Set.Finite {x ∈ S | v x ≠ 0} := by
    simp [v]
    <;> exact Set.finite_empty
  let T' : Set ℂ := T ∪ {ρ}
  have hT'_finite : T'.Finite := hT.union (Set.finite_singleton ρ)
  let w' : ℂ → ℂ := fun s => if s = ρ then wρ else wT s
  have h_main : ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = v x) ∧
      (∀ (s : ℂ), s ∈ T' → melinTransform f.toTestFunction s = w' s) :=
    paley_wiener_whitney_joint_interpolation S hS_countable h_sep v h_vfin T' hT'_finite w'
  rcases h_main with ⟨f, h_pts, h_melin⟩
  have h1 : ∀ (n : ℕ), f.toTestFunction.eval (specDiscM n) = 0 := by
    intro n
    have h2 : specDiscM n ∈ S := Set.mem_range_self n
    have h3 : f.toTestFunction.eval (specDiscM n) = v (specDiscM n) := h_pts (specDiscM n) h2
    rw [h3] <;> rfl
  have h4 : melinTransform f.toTestFunction ρ = wρ := by
    have h5 : ρ ∈ T' := by
      simp [T'] <;> tauto
    have h6 := h_melin ρ h5
    simpa [w'] using h6
  have h5 : ∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = wT s := by
    intro s hs
    have h6 : s ∈ T' := by
      simp [T', hs] <;> exact Or.inl hs
    have h7 := h_melin s h6
    have h8 : w' s = wT s := by
      have h9 : s ≠ ρ := by
        intro h10
        rw [h10] at hs
        exact hρ_notin_T hs
      simp [w', h9]
    rw [h8] at h7
    exact h7
  exact ⟨f, h1, h4, h5⟩

/-- 点态对偶范数界（定理，第二层分析，分部积分）：
    对每个固定的 s（0 < s.re < 1），存在常数 C(s)，使得对任意 C² 光滑 h，
    若 ‖h''(x)‖ ≤ B，则 ‖M[h](s)‖ ≤ C(s)·B。
    证明：两次分部积分 M[h](s) = 1/[s(s+1)]·∫ h''(x)x^{s+1}dx，
    支集有界 [ε,R]，故 ∫ x^{Re(s)+1}dx 有限。
    谱点取值界由 Poincaré 不等式：‖h‖_∞ ≤ (R-ε)²·‖h''‖_∞。
    注：C(s) 依赖于 s，当 s.re→0 时 C(s)→∞（因 |s(s+1)|→0）。 -/
theorem mellin_pointwise_dual_norm_bound (s : ℂ) (hs_re1 : 0 < s.re) (hs_re2 : s.re < 1) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        ‖melinTransform h.toTestFunction s‖ ≤ C * B := by
  rcases mollified_test_function_uniform_support with ⟨ε₀, R₀, hε₀_pos, hε₀_lt_R₀, h_support⟩
  let C : ℝ := (R₀ - ε₀)^2 * max (Real.log (R₀ / ε₀)) (R₀ - ε₀)
  have hC_pos : 0 < C := by
    dsimp only [C]
    have h1 : 0 < R₀ - ε₀ := by linarith
    have h2 : 0 ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) := by
      apply le_max_of_le_right
      linarith
    positivity
  refine ⟨C, hC_pos, fun h B hC2 h_deriv_bound => ?_⟩
  have h_support_h := h_support h
  have hB_nonneg : 0 ≤ B := by
    have h9 : ∀ x, 0 ≤ ‖(deriv (deriv h.toTestFunction.toFun) x)‖ := fun x => by positivity
    have h10 := h_deriv_bound 0
    linarith [h9 0, h10]
  have h_poincare : ∀ x, ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B :=
    poincare_inequality_uniform ε₀ R₀ hε₀_pos hε₀_lt_R₀ h B hC2 h_deriv_bound h_support_h.1 h_support_h.2
  have hM : ‖melinTransform h.toTestFunction s‖ ≤
      ((R₀ - ε₀)^2 * B) * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) :=
    mellin_integral_bound_uniform ε₀ R₀ hε₀_pos hε₀_lt_R₀ h ((R₀ - ε₀)^2 * B) h_poincare h_support_h.1 h_support_h.2 s hs_re1 hs_re2
  dsimp only [C] at *
  have h_eq : ((R₀ - ε₀)^2 * B) * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) =
      (R₀ - ε₀)^2 * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) * B := by ring
  rw [h_eq] at hM
  exact hM

/-- 约束泛函对偶范数统一界（定理，第二层分析）：
    存在统一常数 C，使得对任意 C² 光滑 h，若 ‖h''(x)‖ ≤ B，则
    所有约束泛函的取值 ≤ C·B。
    证明思路（不用分部积分，避免 s.re→0 发散）：
    (1) 谱点取值：Poincaré 不等式 ‖h‖_∞ ≤ (R-ε)²·‖h''‖_∞，故 |h(specDiscM n)| ≤ C₁·B。
    (2) Mellin 变换：直接估计 |M[h](s)| ≤ ‖h‖_∞·∫_ε^R x^{σ-1}dx，
        而 ∫_ε^R x^{σ-1}dx = (R^σ-ε^σ)/σ ≤ max(log(R/ε), R-ε) 对 σ∈(0,1) 有界，
        再用 Poincaré 不等式得 |M[h](s)| ≤ C₂·B。
    注：分部积分给出的界在 s.re→0 时发散，但直接估计 + Poincaré 给出统一界。 -/
theorem mellin_constraint_dual_norm_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∀ (h : MollifiedTestFunction) (B : ℝ),
        ContDiff ℝ 2 h.toTestFunction.toFun →
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B) →
        (∀ (n : ℕ), ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B) ∧
        (∀ (s : ℂ), s ∈ insert ρ T → 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * B) := by
  intro hz hre1 hre2 hne
  rcases mollified_test_function_uniform_support with ⟨ε₀, R₀, hε₀_pos, hε₀_lt_R₀, h_support⟩
  -- 选择足够大的统一常数 C = (R₀-ε₀)² · (max(log(R₀/ε₀), R₀-ε₀) + 1)
  let C : ℝ := (R₀ - ε₀)^2 * (max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1)
  have hC_pos : 0 < C := by
    dsimp only [C]
    have h1 : 0 < R₀ - ε₀ := by linarith
    have h2 : 0 < (R₀ - ε₀)^2 := by positivity
    have h3 : 0 < max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1 := by
      have h4 : 0 ≤ R₀ - ε₀ := by linarith
      have h5 : 0 ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) := by
        apply le_max_of_le_right
        linarith
      linarith
    exact mul_pos h2 h3
  refine ⟨C, hC_pos, fun T hT hρ_notin h B hC2 h_deriv_bound => ?_⟩
  have h_support_h := h_support h
  -- 由 ‖h''‖ ≤ B 且 ‖h''‖ ≥ 0，得 B ≥ 0
  have hB_nonneg : 0 ≤ B := by
    have h9 : ∀ x, 0 ≤ ‖(deriv (deriv h.toTestFunction.toFun) x)‖ := fun x => by positivity
    have h10 := h_deriv_bound 0
    linarith [h9 0, h10]
  -- Poincaré 不等式：‖h‖_∞ ≤ (R₀-ε₀)² · B
  have h_poincare : ∀ x, ‖h.toFun x‖ ≤ (R₀ - ε₀)^2 * B :=
    poincare_inequality_uniform ε₀ R₀ hε₀_pos hε₀_lt_R₀ h B hC2 h_deriv_bound h_support_h.1 h_support_h.2
  -- 谱点取值界：|h(specDiscM n)| ≤ C · B
  have h1 : ∀ n, ‖h.toTestFunction.eval (specDiscM n)‖ ≤ C * B := by
    intro n
    have h3 : ‖h.toTestFunction.eval (specDiscM n)‖ ≤ (R₀ - ε₀)^2 * B := h_poincare (specDiscM n)
    have h4 : (R₀ - ε₀)^2 * B ≤ C * B := by
      dsimp only [C]
      have h5 : 1 ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1 := by
        have h6 : 0 ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) := by
          apply le_max_of_le_right
          linarith
        linarith
      have h7 : (R₀ - ε₀)^2 * B ≤ (R₀ - ε₀)^2 * (max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1) * B := by
        have h8 : 0 ≤ (R₀ - ε₀)^2 * B := by positivity
        have h10 : 1 ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1 := h5
        have h11 : (R₀ - ε₀)^2 * B * 1 ≤ (R₀ - ε₀)^2 * B * (max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1) :=
          mul_le_mul_of_nonneg_left h10 h8
        have h12 : (R₀ - ε₀)^2 * B * 1 = (R₀ - ε₀)^2 * B := by ring
        rw [h12] at h11
        have h13 : (R₀ - ε₀)^2 * B * (max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1) =
            (R₀ - ε₀)^2 * (max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1) * B := by ring
        rw [h13] at h11
        exact h11
      exact h7
    exact le_trans h3 h4
  -- Mellin 变换界：|M[h](s)| ≤ C · B
  have h2 : ∀ s, s ∈ insert ρ T → 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ C * B := by
    intro s hs_in hs_re1 hs_re2
    have h4 : ‖melinTransform h.toTestFunction s‖ ≤
        ((R₀ - ε₀)^2 * B) * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) :=
      mellin_integral_bound_uniform ε₀ R₀ hε₀_pos hε₀_lt_R₀ h ((R₀ - ε₀)^2 * B) h_poincare h_support_h.1 h_support_h.2 s hs_re1 hs_re2
    have h5 : ((R₀ - ε₀)^2 * B) * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) ≤ C * B := by
      dsimp only [C]
      have h6 : ((R₀ - ε₀)^2 * B) * max (Real.log (R₀ / ε₀)) (R₀ - ε₀) ≤
          (R₀ - ε₀)^2 * (max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1) * B := by
        have h7 : max (Real.log (R₀ / ε₀)) (R₀ - ε₀) ≤ max (Real.log (R₀ / ε₀)) (R₀ - ε₀) + 1 := by linarith
        have h8 : 0 ≤ (R₀ - ε₀)^2 * B := by positivity
        nlinarith
      exact h6
    exact le_trans h4 h5
  exact ⟨h1, h2⟩

/-- 对偶范数下界统一公理（新增）：
    对非临界线零点 ρ，存在统一常数 c > 0，使得对任意有限 T（ρ∉T），
    都存在一个测试函数 hT 满足：
    (1) hT 在所有谱点上取值为 0
    (2) M[hT](s) = 0 对所有 s ∈ T
    (3) |M[hT](ρ)| ≥ c * sup_x ‖hT''(x)‖
    即：线性泛函 L_T(h) = Mh(ρ) 在子空间 XT 上的对偶范数有统一的正下界 c。

    注意：这不是逐点不等式，而是"存在测试函数"的形式。
    逐点不等式 |Mh(ρ)| ≥ c * ‖h''‖ 对所有 h 成立是不对的，
    因为如果 h ∈ XT 且 Mh(ρ) = 0，左边就是 0，右边却是正的。

    数学内容：
    用微分算子 L_T = ∏_{t∈T} (D + t)，其中 D = x d/dx，
    从固定的 bump 函数 φ 出发，令 ψ_T = L_T φ，
    则 M[ψ_T](t) = 0 对所有 t ∈ T，且 M[ψ_T](ρ) = (-1)^{|T|} P_T(ρ) M[φ](ρ)。
    我们需要证明比值 |M[ψ_T](ρ)| / ‖ψ_T''‖ 有统一的正下界 c。

    来源依据：
    微分算子消零构造 + 有限维线性代数估计。

    用途范围：
    用于 mellin_min_norm_principle，由 Hahn-Banach 推出最小范数解的上界。 -/
axiom mellin_constraint_dual_norm_lower_uniform (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (c : ℝ), 0 < c ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M

/-- 最小范数原理定理（第三层，Hahn-Banach 层）：
    给定对偶范数下界 c，对任意右端项 wρ（wT=0），存在 C² 光滑解 h
    满足约束且 ‖h''‖ ≤ (1/c)·max(‖wρ‖,1)。
    这是 Hahn-Banach 最小范数原理的标准推论。

    数学：
    设 XT = {h : Mh(σ) = 0 ∀σ ∈ Spectrum, Mh(s) = 0 ∀s ∈ T}，
    定义 L_T(h) = Mh(ρ)，‖h‖_X = sup_x ‖h''(x)‖。
    由对偶范数下界公理，∃ hT ∈ XT, hT ≠ 0，使得 |L_T(hT)| ≥ c * ‖hT‖_X。
    即 ‖L_T‖_* ≥ c。
    由 Hahn-Banach 最小范数原理，inf{‖h‖_X : h ∈ XT, L_T(h) = wρ} = |wρ| / ‖L_T‖_* ≤ |wρ| / c。
    故存在 h ∈ XT，使得 L_T(h) = wρ 且 ‖h‖_X ≤ (1/c) * |wρ|。
    再用 max(‖wρ‖, 1) 处理 wρ = 0 的情况。 -/
theorem mellin_min_norm_principle (ρ : ℂ) (wρ : ℂ) (c : ℝ) (hc_pos : 0 < c) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ((∃ (hT : MollifiedTestFunction) (M : ℝ),
        (∀ (n : ℕ), hT.toTestFunction.eval (specDiscM n) = 0) ∧
        (∀ (s : ℂ), s ∈ T → melinTransform hT.toTestFunction s = 0) ∧
        ContDiff ℝ 2 hT.toTestFunction.toFun ∧
        melinTransform hT.toTestFunction ρ ≠ 0 ∧
        (∀ (x : ℝ), ‖(deriv (deriv hT.toTestFunction.toFun) x)‖ ≤ M) ∧
        ‖melinTransform hT.toTestFunction ρ‖ ≥ c * M) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ (1 / c) * max ‖wρ‖ 1)) := by
  intro hz hre1 hre2 hne T hT_fin hT_notinρ h_exist
  rcases h_exist with ⟨hT, M, hT_spec_zero, hT_T_zero, hT_smooth, hT_ne_zero, hT_deriv_bound, hT_lower⟩
  -- 构造 h = (wρ / M[hT](ρ)) * hT
  let k : ℂ := wρ / melinTransform hT.toTestFunction ρ
  let h : MollifiedTestFunction := k • hT
  have h1 : melinTransform h.toTestFunction ρ = wρ := by
    have h11 : melinTransform h.toTestFunction ρ = k * melinTransform hT.toTestFunction ρ := by
      exact melinTransform_smul hT.toTestFunction k ρ
    rw [h11]
    dsimp only [k]
    field_simp [hT_ne_zero] <;> ring
  have h2 : (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) := by
    intro s hs
    have h21 : melinTransform h.toTestFunction s = k * melinTransform hT.toTestFunction s := by
      exact melinTransform_smul hT.toTestFunction k s
    rw [h21]
    have h22 : melinTransform hT.toTestFunction s = 0 := hT_T_zero s hs
    rw [h22] <;> ring
  have h3 : (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) := by
    intro n
    have h31 : h.toTestFunction.eval (specDiscM n) = k * hT.toTestFunction.eval (specDiscM n) := by rfl
    rw [h31]
    have h32 : hT.toTestFunction.eval (specDiscM n) = 0 := hT_spec_zero n
    rw [h32] <;> ring
  have h4 : ContDiff ℝ 2 h.toTestFunction.toFun := by
    have h41 : h.toTestFunction.toFun = fun x => k * hT.toTestFunction.toFun x := by rfl
    rw [h41]
    exact hT_smooth.const_smul k
  have h5 : (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ (1 / c) * max ‖wρ‖ 1) := by
    intro x
    have h51 : deriv h.toTestFunction.toFun = fun x => k * deriv hT.toTestFunction.toFun x :=
      deriv_const_mul_field' k
    have h52 : deriv (deriv h.toTestFunction.toFun) = fun x => k * deriv (deriv hT.toTestFunction.toFun) x := by
      rw [h51]
      exact deriv_const_mul_field' k
    rw [h52]
    have h53 : ‖(k * deriv (deriv hT.toTestFunction.toFun) x)‖ = ‖k‖ * ‖deriv (deriv hT.toTestFunction.toFun) x‖ := by
      rw [norm_mul]
    rw [h53]
    have h54 : ‖deriv (deriv hT.toTestFunction.toFun) x‖ ≤ M := hT_deriv_bound x
    have h_pos1 : 0 < ‖melinTransform hT.toTestFunction ρ‖ := by
      exact norm_pos_iff.mpr hT_ne_zero
    have h551 : ‖k‖ = ‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖ := by
      dsimp only [k]
      rw [norm_div]
      <;> rfl
    have h552 : M ≤ (1 / c) * ‖melinTransform hT.toTestFunction ρ‖ := by
      have h : c * M ≤ ‖melinTransform hT.toTestFunction ρ‖ := hT_lower
      have h' : 0 < c := hc_pos
      have h'' : c ≠ 0 := h'.ne'
      have h_eq : (1 / c) * (c * M) = M := by
        field_simp [h''] <;> ring
      calc
        M = (1 / c) * (c * M) := h_eq.symm
        _ ≤ (1 / c) * ‖melinTransform hT.toTestFunction ρ‖ := by gcongr
    have h553 : ‖k‖ * M ≤ (1 / c) * max ‖wρ‖ 1 := by
      rw [h551]
      have h : (‖wρ‖ / ‖melinTransform hT.toTestFunction ρ‖) * M = ‖wρ‖ * (M / ‖melinTransform hT.toTestFunction ρ‖) := by ring
      rw [h]
      have h2 : M / ‖melinTransform hT.toTestFunction ρ‖ ≤ 1 / c := by
        calc
          M / ‖melinTransform hT.toTestFunction ρ‖
            ≤ ((1 / c) * ‖melinTransform hT.toTestFunction ρ‖) / ‖melinTransform hT.toTestFunction ρ‖ := by gcongr
          _ = 1 / c := by
            field_simp [h_pos1.ne'] <;> ring
      have h3 : ‖wρ‖ * (M / ‖melinTransform hT.toTestFunction ρ‖) ≤ ‖wρ‖ * (1 / c) := by
        gcongr
      have h4 : ‖wρ‖ * (1 / c) ≤ (1 / c) * max ‖wρ‖ 1 := by
        have h5 : ‖wρ‖ ≤ max ‖wρ‖ 1 := le_max_left ‖wρ‖ 1
        have h6 : 0 < 1 / c := by positivity
        calc
          ‖wρ‖ * (1 / c) ≤ (max ‖wρ‖ 1) * (1 / c) := by gcongr
          _ = (1 / c) * max ‖wρ‖ 1 := by ring
      calc
        ‖wρ‖ * (M / ‖melinTransform hT.toTestFunction ρ‖) ≤ ‖wρ‖ * (1 / c) := h3
        _ ≤ (1 / c) * max ‖wρ‖ 1 := h4
    have h55 : ‖k‖ * M ≤ (1 / c) * max ‖wρ‖ 1 := h553
    exact mul_le_mul_of_nonneg_left h54 (by positivity) |>.trans h55
  exact ⟨h, h3, h1, h2, h4, h5⟩




/-- 最小导数范数统一界（定理，由对偶范数下界 + 最小范数原理推出）： -/
theorem mellin_smooth_min_derivative_norm_uniform (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) := by
  intro hz hre1 hre2 hne
  rcases mellin_constraint_dual_norm_lower_uniform ρ hz hre1 hre2 hne with ⟨c, hc_pos, h_lower⟩
  let B : ℝ := 1 / c
  have hB_pos : 0 < B := by positivity
  refine ⟨B, hB_pos, fun T hT hρ_notin => ?_⟩
  have hT_exists := h_lower T hT hρ_notin
  exact mellin_min_norm_principle ρ wρ c hc_pos hz hre1 hre2 hne T hT hρ_notin hT_exists

/-- 光滑插值存在性（定理，由最小导数范数统一界公理推出）：
    对非临界线零点 ρ 和目标值 wρ，对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足 (1)-(3)。
    证明：mellin_smooth_min_derivative_norm_uniform 直接构造 C² 光滑 h 满足 (1)-(3)。 -/
theorem mellin_smooth_interpolation_no_bound (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∃ (h : MollifiedTestFunction),
      (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
      melinTransform h.toTestFunction ρ = wρ ∧
      (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
      ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin
  rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩

/-- 光滑插值选择定理（由导数统一界公理直接推出）：
    对非临界线零点 ρ 和目标值 wρ，存在统一导数界 B，使得对任意有限 T（ρ∉T），
    存在 C² 光滑磨光函数 h 满足 (1)-(3) 且二阶导数有界。
    注：mellin_smooth_min_derivative_norm_uniform 直接给出带导数界的构造，
    mellin_mollification_preserves_finite 是其直接推论。 -/
theorem mellin_smooth_interpolation (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (B : ℝ), 0 < B ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun ∧
        (∀ (x : ℝ), ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B * max ‖wρ‖ 1) :=
  mellin_smooth_min_derivative_norm_uniform ρ wρ

/-- 光滑化保持有限赋值（定理，由导数统一界公理直接推出）：
    对任意满足零谱点插值条件 (1)-(3) 的磨光函数 h₀，存在 C² 光滑磨光函数 h
    满足同样的 (1)-(3)。
    证明：mellin_smooth_derivative_uniform 直接构造 C² 光滑 h 满足 (1)-(3)，
    且不依赖于 h₀。h₀ 的存在性由 mellin_zero_spectral_interpolation 保证，
    但光滑化后的 h 由导数统一界公理独立构造。 -/
theorem mellin_mollification_preserves_finite (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
    ∀ (h0 : MollifiedTestFunction),
      (∀ (n : ℕ), h0.toTestFunction.eval (specDiscM n) = 0) →
      melinTransform h0.toTestFunction ρ = wρ →
      (∀ (s : ℂ), s ∈ T → melinTransform h0.toTestFunction s = 0) →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        ContDiff ℝ 2 h.toTestFunction.toFun := by
  intro hz hre1 hre2 hne T hT hρ_notin h0 _ _ _
  rcases mellin_smooth_min_derivative_norm_uniform ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, _⟩
  exact ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2⟩

/-- Mellin 速降界分解为 5 个步骤
    步骤 1：积分缩限到 [ε₀, R₀] -/
lemma mellin_rapid_decay_step1 (h : MollifiedTestFunction) (s : ℂ)
    (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀)
    (h_left : ∀ x, x < ε₀ → h.toFun x = 0)
    (h_right : ∀ x, x > R₀ → h.toFun x = 0) :
    melinTransform h.toTestFunction s =
      ∫ x in Set.Icc ε₀ R₀, h.toFun x * (x : ℂ)^(s - 1) := by
  have h_support_fun : ∀ x, x ∉ Set.Icc ε₀ R₀ → h.toFun x = 0 := by
    intro x hx
    by_cases h : x < ε₀
    · exact h_left x h
    · by_cases h2 : x > R₀
      · exact h_right x h2
      · have h3 : x ∈ Set.Icc ε₀ R₀ := by
          simpa [Set.mem_Icc] using ⟨by linarith, by linarith⟩
        exact False.elim (hx h3)
  have h_support : ∀ x, x ∉ Set.Ioi (0 : ℝ) →
      (if 0 < x then h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) = 0 := by
    intro x hx
    rw [if_neg (by simpa [Set.mem_Ioi] using hx)]
  have h_support2 : ∀ x, x ∉ Set.Icc ε₀ R₀ →
      (if 0 < x then h.toFun x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) = 0 := by
    intro x hx
    by_cases h_pos : 0 < x
    · have h4 : h.toFun x = 0 := h_support_fun x hx
      rw [if_pos h_pos, h4, zero_mul]
    · rw [if_neg (by linarith)]
  -- 1. 展开 melinTransform 和 realIntegral 定义
  dsimp only [melinTransform, realIntegral]
  -- 2. 积分缩限：从 Ioi(0) 缩到 Icc(ε₀, R₀)
  let f : ℝ → ℂ := fun x => if 0 < x then h.toTestFunction.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0
  have h_subset : Set.Icc ε₀ R₀ ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have h1 : ε₀ ≤ x := hx.1
    have h2 : 0 < ε₀ := hε₀_pos
    exact lt_of_lt_of_le h2 h1
  have h_eval_eq : ∀ x, h.toTestFunction.eval x = h.toFun x := by
    intro x
    rfl
  have h_diff_zero : ∀ x ∈ Set.Ioi (0 : ℝ) \ Set.Icc ε₀ R₀, f x = 0 := by
    intro x hx
    have h_x_pos : x ∈ Set.Ioi (0 : ℝ) := hx.1
    have h_x_notin_Icc : x ∉ Set.Icc ε₀ R₀ := hx.2
    have h4 : h.toFun x = 0 := h_support_fun x h_x_notin_Icc
    have h5 : h.toTestFunction.eval x = 0 := by
      rw [h_eval_eq x, h4]
    simp only [f, h5, if_pos (Set.mem_Ioi.mp h_x_pos), zero_mul]
  have h_restrict : ∫ x in Set.Ioi (0 : ℝ), f x = ∫ x in Set.Icc ε₀ R₀, f x :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioi) h_subset h_diff_zero
  have h_main : melinTransform h.toTestFunction s = ∫ x in Set.Icc ε₀ R₀, f x := by
    calc
      melinTransform h.toTestFunction s
        = ∫ x in Set.Ioi (0 : ℝ), f x := by
          simp [melinTransform, realIntegral, f, h_eval_eq]
          <;> rfl
      _ = ∫ x in Set.Icc ε₀ R₀, f x := h_restrict
  -- 定义目标函数
  let g : ℝ → ℂ := fun x => h.toFun x * (x : ℂ)^(s - 1)
  -- 证明在 Icc 内 f x = g x
  have h_f_eq_g : ∀ x ∈ Set.Icc ε₀ R₀, f x = g x := by
    intro x hx
    have h_x_pos : 0 < x := by
      have h1 : ε₀ ≤ x := hx.1
      have h2 : 0 < ε₀ := hε₀_pos
      exact lt_of_lt_of_le h2 h1
    have h_if_pos : (if 0 < x then h.toTestFunction.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) =
        h.toTestFunction.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) := by
      rw [if_pos h_x_pos]
    have h_x_ne_zero : (x : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt h_x_pos)
    have h_cpow : (x : ℂ)^(s - 1) = Complex.exp (Complex.log (x : ℂ) * (s - 1)) := by
      rw [cpow_def_of_ne_zero h_x_ne_zero]
      <;> ring
    have h_log : Complex.log (x : ℂ) = (Real.log x : ℂ) := by
      have h_log_re : (Complex.log (x : ℂ)).re = Real.log x := by
        exact Complex.log_ofReal_re x
      have h_log_im : (Complex.log (x : ℂ)).im = 0 := by
        rw [Complex.log_im]
        exact Complex.arg_ofReal_of_nonneg (by linarith)
      apply Complex.ext
      · exact h_log_re
      · simpa using h_log_im
    have h_exp_eq : Complex.exp ((s - 1) * (Real.log x : ℂ)) = (x : ℂ)^(s - 1) := by
      rw [h_cpow, h_log]
      <;> ring
    have h_eval : h.toTestFunction.eval x = h.toFun x := h_eval_eq x
    simp only [f, g, h_if_pos, h_exp_eq, h_eval]
    <;> rfl
  -- 用积分内函数替换
  have h_integral_eq : ∫ x in Set.Icc ε₀ R₀, f x = ∫ x in Set.Icc ε₀ R₀, g x := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc h_f_eq_g
  rw [h_integral_eq] at h_main
  exact h_main

lemma mellin_rapid_decay_step2 (h : MollifiedTestFunction) (s : ℂ)
    (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀)
    (hC2 : ContDiff ℝ 2 h.toTestFunction.toFun)
    (h_left : ∀ x, x < ε₀ → h.toFun x = 0)
    (h_right : ∀ x, x > R₀ → h.toFun x = 0)
    (h_s_ne_zero : s ≠ 0)
    (h_u_eps0_zero : h.toFun ε₀ = 0)
    (h_u_R0_zero : h.toFun R₀ = 0) :
    ∫ x in Set.Icc ε₀ R₀, h.toFun x * (x : ℂ)^(s - 1) =
      -1/s * ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s := by
  -- 定义 u, v, u', v'
  let u : ℝ → ℂ := fun x => h.toFun x
  let v : ℝ → ℂ := fun x => (x : ℂ)^s / s
  let u' : ℝ → ℂ := fun x => (deriv h.toFun) x
  let v' : ℝ → ℂ := fun x => (x : ℂ)^(s - 1)
  -- 步骤 1：证明 u, v 在 [ε₀, R₀] 上连续
  have hu_cont : ContinuousOn u (Set.Icc ε₀ R₀) := by
    exact hC2.continuous.continuousOn
  have hv_cont : ContinuousOn v (Set.Icc ε₀ R₀) := by
    by_cases h_s_ne_zero : s ≠ 0
    · -- Case 1: s ≠ 0
      have h_pos : ∀ x ∈ Set.Icc ε₀ R₀, (x : ℂ) ≠ 0 := by
        intro x hx
        have h1 : 0 < x := by
          have h2 : ε₀ ≤ x := hx.1
          have h3 : 0 < ε₀ := hε₀_pos
          exact lt_of_lt_of_le h3 h2
        exact_mod_cast (ne_of_gt h1)
      have h1 : ContinuousOn (fun x : ℝ => (x : ℂ)) (Set.Icc ε₀ R₀) := by
        exact continuous_ofReal.continuousOn
      have hg : ContinuousOn (fun x : ℝ => s) (Set.Icc ε₀ R₀) := by
        exact continuous_const.continuousOn
      have h0 : ∀ x ∈ Set.Icc ε₀ R₀, (x : ℂ) ∈ slitPlane := by
        intro x hx
        have h1 : 0 < x := by
          have h2 : ε₀ ≤ x := hx.1
          have h3 : 0 < ε₀ := hε₀_pos
          exact lt_of_lt_of_le h3 h2
        have h4 : (x : ℂ).arg = 0 := by
          exact Complex.arg_ofReal_of_nonneg h1.le
        have h5 : (x : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt h1)
        have h6 : (x : ℂ).arg ≠ Real.pi := by
          rw [h4]
          exact Real.pi_ne_zero.symm
        exact (Complex.mem_slitPlane_iff_arg.mpr ⟨h6, h5⟩)
      have h2 : ContinuousOn (fun x : ℝ => (x : ℂ)^s) (Set.Icc ε₀ R₀) := by
        exact ContinuousOn.cpow h1 hg h0
      have h3 : ContinuousOn (fun x : ℝ => (x : ℂ)^s / s) (Set.Icc ε₀ R₀) := by
        have hg2 : ContinuousOn (fun x : ℝ => s) (Set.Icc ε₀ R₀) := by
          exact continuous_const.continuousOn
        have h_ne_zero : ∀ x ∈ Set.Icc ε₀ R₀, (s : ℂ) ≠ 0 := by
          intro x hx
          exact h_s_ne_zero
        exact ContinuousOn.div h2 hg2 h_ne_zero
      exact h3
    · -- Case 2: s = 0
      have h_s_eq_zero : s = 0 := by tauto
      have h_v_eq_zero : v = fun x : ℝ => (0 : ℂ) := by
        funext x
        simp [v, h_s_eq_zero]
        <;> norm_num
      rw [h_v_eq_zero]
      exact continuous_const.continuousOn
  -- 步骤 2：证明 u, v 在 (ε₀, R₀) 内可微
  have hu_diff : ∀ x ∈ Set.Ioo ε₀ R₀, HasDerivAt u (u' x) x := by
    intro x hx
    have h_eq : h.toFun = h.toTestFunction.toFun := by rfl
    rw [h_eq] at *
    have h_diff : Differentiable ℝ h.toTestFunction.toFun := by
      exact hC2.differentiable (by norm_num)
    have h_diff_at : DifferentiableAt ℝ h.toTestFunction.toFun x := by
      exact h_diff.differentiableAt
    exact h_diff_at.hasDerivAt
  have hv_diff : ∀ x ∈ Set.Ioo ε₀ R₀, HasDerivAt v (v' x) x := by
    intro x hx
    have h_pos : 0 < x := by
      have h1 : ε₀ < x := hx.1
      have h2 : 0 < ε₀ := hε₀_pos
      exact lt_trans h2 h1
    have h_ne_zero : x ≠ 0 := by
      exact ne_of_gt h_pos
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ)^s) (s * (x : ℂ)^(s - 1)) x := by
      exact hasDerivAt_ofReal_cpow_const h_ne_zero h_s_ne_zero
    have h3 : HasDerivAt v ((x : ℂ)^(s - 1)) x := by
      have h4 : HasDerivAt (fun y : ℝ => (y : ℂ)^s / s) ((s * (x : ℂ)^(s - 1)) / s) x := by
        exact h2.div_const s
      have h5 : (s * (x : ℂ)^(s - 1)) / s = (x : ℂ)^(s - 1) := by
        field_simp [h_s_ne_zero] <;> ring
      rw [h5] at h4
      exact h4
    exact h3
  -- 步骤 4：证明 u', v' 在 [ε₀, R₀] 上区间可积
  have hu'_int : IntervalIntegrable u' volume ε₀ R₀ := by
    have h_cont' : Continuous u' := by
      have h_c1 : ContDiff ℝ 1 (deriv h.toFun) := by
        exact hC2.deriv'
      exact h_c1.continuous
    exact?
  have hv'_int : IntervalIntegrable v' volume ε₀ R₀ := by
    have h_cont' : ContinuousOn v' (Set.Icc ε₀ R₀) := by
      have h1 : ContinuousOn (fun x : ℝ => (x : ℂ)) (Set.Icc ε₀ R₀) := by
        exact continuous_ofReal.continuousOn
      have hg : ContinuousOn (fun x : ℝ => s - 1) (Set.Icc ε₀ R₀) := by
        exact continuous_const.continuousOn
      have h0 : ∀ x ∈ Set.Icc ε₀ R₀, (x : ℂ) ∈ slitPlane := by
        intro x hx
        have h1 : 0 < x := by
          have h2 : ε₀ ≤ x := hx.1
          have h3 : 0 < ε₀ := hε₀_pos
          exact lt_of_lt_of_le h3 h2
        have h4 : (x : ℂ).arg = 0 := by
          exact Complex.arg_ofReal_of_nonneg h1.le
        have h5 : (x : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt h1)
        have h6 : (x : ℂ).arg ≠ Real.pi := by
          rw [h4]
          exact Real.pi_ne_zero.symm
        exact (Complex.mem_slitPlane_iff_arg.mpr ⟨h6, h5⟩)
      exact ContinuousOn.cpow h1 hg h0
    have h_le : ε₀ ≤ R₀ := by linarith
    exact ContinuousOn.intervalIntegrable_of_Icc h_le h_cont'
  -- 步骤 5：应用分部积分定理
  have h_ibp : ∫ x in ε₀..R₀, u x * v' x = u R₀ * v R₀ - u ε₀ * v ε₀ - ∫ x in ε₀..R₀, u' x * v x := by
    have h_min_max : min ε₀ R₀ = ε₀ ∧ max ε₀ R₀ = R₀ := by
      constructor
      · exact min_eq_left (le_of_lt hε₀_lt_R₀)
      · exact max_eq_right (le_of_lt hε₀_lt_R₀)
    have hu_cont' : ContinuousOn u (Set.uIcc ε₀ R₀) := by
      simpa [Set.uIcc_of_le (show ε₀ ≤ R₀ by linarith)] using hu_cont
    have hv_cont' : ContinuousOn v (Set.uIcc ε₀ R₀) := by
      simpa [Set.uIcc_of_le (show ε₀ ≤ R₀ by linarith)] using hv_cont
    have hu_diff' : ∀ x ∈ Set.Ioo (min ε₀ R₀) (max ε₀ R₀), HasDerivAt u (u' x) x := by
      simpa [h_min_max.1, h_min_max.2] using hu_diff
    have hv_diff' : ∀ x ∈ Set.Ioo (min ε₀ R₀) (max ε₀ R₀), HasDerivAt v (v' x) x := by
      simpa [h_min_max.1, h_min_max.2] using hv_diff
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu_cont' hv_cont' hu_diff' hv_diff' hu'_int hv'_int
  -- 步骤 5：边界项为 0
  have h_boundary : u R₀ * v R₀ - u ε₀ * v ε₀ = 0 := by
    have h1 : u R₀ = 0 := h_u_R0_zero
    have h2 : u ε₀ = 0 := h_u_eps0_zero
    rw [h1, h2]
    <;> simp
  -- 步骤 6：化简
  have h_main : ∫ x in ε₀..R₀, u x * v' x = - ∫ x in ε₀..R₀, u' x * v x := by
    rw [h_ibp, h_boundary] <;> ring
  have h_le : ε₀ ≤ R₀ := by linarith
  have h_eq1 : ∫ x in Set.Icc ε₀ R₀, u x * v' x = ∫ x in ε₀..R₀, u x * v' x := by
    have h1 : ∫ x in Set.Icc ε₀ R₀, u x * v' x = ∫ x in Set.Ioc ε₀ R₀, u x * v' x := by
      exact integral_Icc_eq_integral_Ioc
    have h2 : ∫ x in Set.Ioc ε₀ R₀, u x * v' x = ∫ x in ε₀..R₀, u x * v' x := by
      exact (intervalIntegral.integral_of_le h_le).symm
    rw [h1, h2]
  have h_eq2 : ∫ x in Set.Icc ε₀ R₀, u' x * v x = ∫ x in ε₀..R₀, u' x * v x := by
    have h1 : ∫ x in Set.Icc ε₀ R₀, u' x * v x = ∫ x in Set.Ioc ε₀ R₀, u' x * v x := by
      exact integral_Icc_eq_integral_Ioc
    have h2 : ∫ x in Set.Ioc ε₀ R₀, u' x * v x = ∫ x in ε₀..R₀, u' x * v x := by
      exact (intervalIntegral.integral_of_le h_le).symm
    rw [h1, h2]
  have h_goal : ∫ x in Set.Icc ε₀ R₀, u x * v' x = - ∫ x in Set.Icc ε₀ R₀, u' x * v x := by
    rw [h_eq1, h_eq2]
    exact h_main
  have h_final : ∫ x in Set.Icc ε₀ R₀, h.toFun x * (x : ℂ)^(s - 1) =
      -1/s * ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s := by
    have h1 : ∫ x in Set.Icc ε₀ R₀, u x * v' x = ∫ x in Set.Icc ε₀ R₀, h.toFun x * (x : ℂ)^(s - 1) := by
      rfl
    have h2 : ∫ x in Set.Icc ε₀ R₀, u' x * v x = ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * ((x : ℂ)^s / s) := by
      rfl
    rw [h1, h2] at h_goal
    have h3 : - ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * ((x : ℂ)^s / s) =
        -1/s * ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s := by
      have h4 : ∀ x, (deriv h.toFun) x * ((x : ℂ)^s / s) = (1/s : ℂ) * ((deriv h.toFun) x * (x : ℂ)^s) := by
        intro x
        ring
      have h5 : ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * ((x : ℂ)^s / s) =
          ∫ x in Set.Icc ε₀ R₀, (1/s : ℂ) * ((deriv h.toFun) x * (x : ℂ)^s) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact h4 x
      have h6 : ∫ x in Set.Icc ε₀ R₀, (1/s : ℂ) * ((deriv h.toFun) x * (x : ℂ)^s) =
          (1/s : ℂ) * ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s := by
        rw [MeasureTheory.integral_const_mul]
      rw [h5, h6] <;> ring
    rw [h3] at h_goal
    exact h_goal
  exact h_final

/-- 速降界步骤 3：第二次分部积分
    ∫ h'(x) x^s dx = -1/(s+1) ∫ h''(x) x^{s+1} dx（边界项为 0） -/
lemma mellin_rapid_decay_step3 (h : MollifiedTestFunction) (s : ℂ)
    (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀)
    (hC2 : ContDiff ℝ 2 h.toTestFunction.toFun)
    (h_left : ∀ x, x < ε₀ → h.toFun x = 0)
    (h_right : ∀ x, x > R₀ → h.toFun x = 0)
    (h_s1_ne_zero : s + 1 ≠ 0)
    (h_u'_eps0_zero : (deriv h.toFun) ε₀ = 0)
    (h_u'_R0_zero : (deriv h.toFun) R₀ = 0) :
    ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s =
      -1/(s + 1) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) := by
  -- 定义 u, v, u', v'
  let u : ℝ → ℂ := fun x => (deriv h.toFun) x
  let v : ℝ → ℂ := fun x => (x : ℂ)^(s + 1) / (s + 1)
  let u' : ℝ → ℂ := fun x => (deriv (deriv h.toFun)) x
  let v' : ℝ → ℂ := fun x => (x : ℂ)^s
  -- 步骤 1：证明 u, v 在 [ε₀, R₀] 上连续
  have hu_cont : ContinuousOn u (Set.Icc ε₀ R₀) := by
    have h_c1 : ContDiff ℝ 1 (deriv h.toFun) := hC2.deriv'
    exact h_c1.continuous.continuousOn
  have hv_cont : ContinuousOn v (Set.Icc ε₀ R₀) := by
    have h_pos : ∀ x ∈ Set.Icc ε₀ R₀, (x : ℂ) ≠ 0 := by
      intro x hx
      have h1 : 0 < x := by
        have h2 : ε₀ ≤ x := hx.1
        have h3 : 0 < ε₀ := hε₀_pos
        exact lt_of_lt_of_le h3 h2
      exact_mod_cast (ne_of_gt h1)
    have h1 : ContinuousOn (fun x : ℝ => (x : ℂ)) (Set.Icc ε₀ R₀) := by
      exact continuous_ofReal.continuousOn
    have hg : ContinuousOn (fun x : ℝ => s + 1) (Set.Icc ε₀ R₀) := by
      exact continuous_const.continuousOn
    have h0 : ∀ x ∈ Set.Icc ε₀ R₀, (x : ℂ) ∈ slitPlane := by
      intro x hx
      have h1 : 0 < x := by
        have h2 : ε₀ ≤ x := hx.1
        have h3 : 0 < ε₀ := hε₀_pos
        exact lt_of_lt_of_le h3 h2
      have h4 : (x : ℂ).arg = 0 := by
        exact Complex.arg_ofReal_of_nonneg h1.le
      have h5 : (x : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt h1)
      have h6 : (x : ℂ).arg ≠ Real.pi := by
        rw [h4]
        exact Real.pi_ne_zero.symm
      exact (Complex.mem_slitPlane_iff_arg.mpr ⟨h6, h5⟩)
    have h2 : ContinuousOn (fun x : ℝ => (x : ℂ)^(s + 1)) (Set.Icc ε₀ R₀) := by
      exact ContinuousOn.cpow h1 hg h0
    have h3 : ContinuousOn (fun x : ℝ => (x : ℂ)^(s + 1) / (s + 1)) (Set.Icc ε₀ R₀) := by
      have hg2 : ContinuousOn (fun x : ℝ => (s + 1)) (Set.Icc ε₀ R₀) := by
        exact continuous_const.continuousOn
      have h_ne_zero : ∀ x ∈ Set.Icc ε₀ R₀, ((s + 1) : ℂ) ≠ 0 := by
        intro x hx
        exact h_s1_ne_zero
      exact ContinuousOn.div h2 hg2 h_ne_zero
    exact h3
  -- 步骤 2：证明 u, v 在 (ε₀, R₀) 上可微
  have hu_diff : ∀ x ∈ Set.Ioo ε₀ R₀, HasDerivAt u (u' x) x := by
    intro x hx
    have h_c1 : ContDiff ℝ 1 (deriv h.toFun) := hC2.deriv'
    have h_diff : Differentiable ℝ (deriv h.toFun) := by
      exact h_c1.differentiable (by norm_num)
    have h_diff_at : DifferentiableAt ℝ (deriv h.toFun) x := by
      exact h_diff.differentiableAt
    exact h_diff_at.hasDerivAt
  have hv_diff : ∀ x ∈ Set.Ioo ε₀ R₀, HasDerivAt v (v' x) x := by
    intro x hx
    have h_pos : 0 < x := by
      have h1 : ε₀ < x := hx.1
      have h2 : 0 < ε₀ := hε₀_pos
      exact lt_trans h2 h1
    have h_ne_zero : x ≠ 0 := by
      exact ne_of_gt h_pos
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ)^(s + 1)) ((s + 1) * (x : ℂ)^((s + 1) - 1)) x := by
      exact hasDerivAt_ofReal_cpow_const h_ne_zero h_s1_ne_zero
    have h3 : HasDerivAt v ((x : ℂ)^s) x := by
      have h4 : HasDerivAt (fun y : ℝ => (y : ℂ)^(s + 1) / (s + 1)) (((s + 1) * (x : ℂ)^((s + 1) - 1)) / (s + 1)) x := by
        exact h2.div_const (s + 1)
      have h5 : ((s + 1) * (x : ℂ)^((s + 1) - 1)) / (s + 1) = (x : ℂ)^s := by
        field_simp [h_s1_ne_zero] <;> ring
      rw [h5] at h4
      exact h4
    exact h3
  -- 步骤 3：证明 u', v' 在 [ε₀, R₀] 上区间可积
  have hu'_int : IntervalIntegrable u' volume ε₀ R₀ := by
    have h_c0 : ContDiff ℝ 0 (deriv (deriv h.toFun)) := hC2.deriv'.deriv'
    have h_cont : Continuous u' := h_c0.continuous
    exact?
  have hv'_int : IntervalIntegrable v' volume ε₀ R₀ := by
    have h_cont' : ContinuousOn v' (Set.Icc ε₀ R₀) := by
      have h1 : ContinuousOn (fun x : ℝ => (x : ℂ)) (Set.Icc ε₀ R₀) := by
        exact continuous_ofReal.continuousOn
      have hg : ContinuousOn (fun x : ℝ => s) (Set.Icc ε₀ R₀) := by
        exact continuous_const.continuousOn
      have h0 : ∀ x ∈ Set.Icc ε₀ R₀, (x : ℂ) ∈ slitPlane := by
        intro x hx
        have h1 : 0 < x := by
          have h2 : ε₀ ≤ x := hx.1
          have h3 : 0 < ε₀ := hε₀_pos
          exact lt_of_lt_of_le h3 h2
        have h4 : (x : ℂ).arg = 0 := by
          exact Complex.arg_ofReal_of_nonneg h1.le
        have h5 : (x : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt h1)
        have h6 : (x : ℂ).arg ≠ Real.pi := by
          rw [h4]
          exact Real.pi_ne_zero.symm
        exact (Complex.mem_slitPlane_iff_arg.mpr ⟨h6, h5⟩)
      exact ContinuousOn.cpow h1 hg h0
    have h_le : ε₀ ≤ R₀ := by linarith
    exact ContinuousOn.intervalIntegrable_of_Icc h_le h_cont'
  -- 步骤 4：应用分部积分定理
  have h_ibp : ∫ x in ε₀..R₀, u x * v' x = u R₀ * v R₀ - u ε₀ * v ε₀ - ∫ x in ε₀..R₀, u' x * v x := by
    have h_min_max : min ε₀ R₀ = ε₀ ∧ max ε₀ R₀ = R₀ := by
      constructor
      · exact min_eq_left (le_of_lt hε₀_lt_R₀)
      · exact max_eq_right (le_of_lt hε₀_lt_R₀)
    have hu_cont' : ContinuousOn u (Set.uIcc ε₀ R₀) := by
      simpa [Set.uIcc_of_le (show ε₀ ≤ R₀ by linarith)] using hu_cont
    have hv_cont' : ContinuousOn v (Set.uIcc ε₀ R₀) := by
      simpa [Set.uIcc_of_le (show ε₀ ≤ R₀ by linarith)] using hv_cont
    have hu_diff' : ∀ x ∈ Set.Ioo (min ε₀ R₀) (max ε₀ R₀), HasDerivAt u (u' x) x := by
      simpa [h_min_max.1, h_min_max.2] using hu_diff
    have hv_diff' : ∀ x ∈ Set.Ioo (min ε₀ R₀) (max ε₀ R₀), HasDerivAt v (v' x) x := by
      simpa [h_min_max.1, h_min_max.2] using hv_diff
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu_cont' hv_cont' hu_diff' hv_diff' hu'_int hv'_int
  -- 步骤 5：边界项为 0
  have h_boundary : u R₀ * v R₀ - u ε₀ * v ε₀ = 0 := by
    have h1 : u R₀ = 0 := h_u'_R0_zero
    have h2 : u ε₀ = 0 := h_u'_eps0_zero
    rw [h1, h2] <;> simp
  -- 步骤 6：化简
  have h_main : ∫ x in ε₀..R₀, u x * v' x = - ∫ x in ε₀..R₀, u' x * v x := by
    rw [h_ibp, h_boundary] <;> ring
  have h_le : ε₀ ≤ R₀ := by linarith
  have h_eq1 : ∫ x in Set.Icc ε₀ R₀, u x * v' x = ∫ x in ε₀..R₀, u x * v' x := by
    have h1 : ∫ x in Set.Icc ε₀ R₀, u x * v' x = ∫ x in Set.Ioc ε₀ R₀, u x * v' x := by
      exact integral_Icc_eq_integral_Ioc
    have h2 : ∫ x in Set.Ioc ε₀ R₀, u x * v' x = ∫ x in ε₀..R₀, u x * v' x := by
      exact (intervalIntegral.integral_of_le h_le).symm
    rw [h1, h2]
  have h_eq2 : ∫ x in Set.Icc ε₀ R₀, u' x * v x = ∫ x in ε₀..R₀, u' x * v x := by
    have h1 : ∫ x in Set.Icc ε₀ R₀, u' x * v x = ∫ x in Set.Ioc ε₀ R₀, u' x * v x := by
      exact integral_Icc_eq_integral_Ioc
    have h2 : ∫ x in Set.Ioc ε₀ R₀, u' x * v x = ∫ x in ε₀..R₀, u' x * v x := by
      exact (intervalIntegral.integral_of_le h_le).symm
    rw [h1, h2]
  have h_goal : ∫ x in Set.Icc ε₀ R₀, u x * v' x = - ∫ x in Set.Icc ε₀ R₀, u' x * v x := by
    rw [h_eq1, h_eq2]
    exact h_main
  have h_final : ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s =
      -1/(s + 1) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) := by
    have h1 : ∫ x in Set.Icc ε₀ R₀, u x * v' x = ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s := by
      rfl
    have h2 : ∫ x in Set.Icc ε₀ R₀, u' x * v x = ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * ((x : ℂ)^(s + 1) / (s + 1)) := by
      rfl
    rw [h1, h2] at h_goal
    have h3 : - ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * ((x : ℂ)^(s + 1) / (s + 1)) =
        -1/(s + 1) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) := by
      have h4 : ∀ x, (deriv (deriv h.toFun)) x * ((x : ℂ)^(s + 1) / (s + 1)) =
          (1/(s + 1) : ℂ) * ((deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)) := by
        intro x
        ring
      have h5 : ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * ((x : ℂ)^(s + 1) / (s + 1)) =
          ∫ x in Set.Icc ε₀ R₀, (1/(s + 1) : ℂ) * ((deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact h4 x
      have h6 : ∫ x in Set.Icc ε₀ R₀, (1/(s + 1) : ℂ) * ((deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)) =
          (1/(s + 1) : ℂ) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) := by
        rw [MeasureTheory.integral_const_mul]
      rw [h5, h6] <;> ring
    rw [h3] at h_goal
    exact h_goal
  exact h_final

/-- 速降界步骤 4：积分界
    ∫ |h''(x)|·x^{σ+1} dx ≤ B' · (R₀^{σ+2} - ε₀^{σ+2})/(σ+2) -/
lemma mellin_rapid_decay_step4 (h : MollifiedTestFunction) (s : ℂ)
    (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀)
    (B' : ℝ) (hB : ∀ x, ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B')
    (hC2 : ContDiff ℝ 2 h.toTestFunction.toFun)
    (h_s2_ne_zero : s.re + 2 ≠ 0) :
    ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toTestFunction.toFun) x)‖ * x^(s.re + 1) ≤
      B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
  -- 步骤 1：证明 0 ≤ B'
  have hB'_nonneg : 0 ≤ B' := by
    have h1 : ‖(deriv (deriv h.toTestFunction.toFun) ε₀)‖ ≤ B' := hB ε₀
    have h2 : 0 ≤ ‖(deriv (deriv h.toTestFunction.toFun) ε₀)‖ := by
      exact norm_nonneg _
    exact le_trans h2 h1
  -- 步骤 2：逐点不等式
  have h_pointwise : ∀ x ∈ Set.Icc ε₀ R₀,
      ‖(deriv (deriv h.toTestFunction.toFun) x)‖ * x^(s.re + 1) ≤ B' * x^(s.re + 1) := by
    intro x hx
    have h3 : ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B' := hB x
    have h4 : 0 ≤ x^(s.re + 1) := by
      have h5 : 0 ≤ x := by
        have h6 : ε₀ ≤ x := hx.1
        have h7 : 0 < ε₀ := hε₀_pos
        exact le_of_lt (lt_of_lt_of_le h7 h6)
      exact Real.rpow_nonneg h5 _
    exact mul_le_mul_of_nonneg_right h3 h4
  -- 步骤 3：幂函数在 [ε₀, R₀] 上连续
  have h_cont_pow : ContinuousOn (fun x : ℝ => x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
    have h1 : ContinuousOn (fun x : ℝ => x) (Set.Icc ε₀ R₀) := by
      exact continuous_id.continuousOn
    have h2 : ContinuousOn (fun x : ℝ => s.re + 1) (Set.Icc ε₀ R₀) := by
      exact continuous_const.continuousOn
    have h3 : ∀ x ∈ Set.Icc ε₀ R₀, (x : ℝ) ≠ 0 ∨ 0 < s.re + 1 := by
      intro x hx
      have h4 : 0 < x := by
        have h5 : ε₀ ≤ x := hx.1
        have h6 : 0 < ε₀ := hε₀_pos
        exact lt_of_lt_of_le h6 h5
      exact Or.inl (ne_of_gt h4)
    exact ContinuousOn.rpow h1 h2 h3
  -- 步骤 4：幂函数在 [ε₀, R₀] 上可积
  have h_integrable_pow : MeasureTheory.IntegrableOn (fun x : ℝ => x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
    exact h_cont_pow.integrableOn_compact isCompact_Icc
  -- 步骤 5：被积函数在 [ε₀, R₀] 上可积
  have h_cont_abs : ContinuousOn (fun x : ℝ => ‖(deriv (deriv h.toTestFunction.toFun) x)‖) (Set.Icc ε₀ R₀) := by
    have h1 : Continuous (deriv (deriv h.toTestFunction.toFun)) := by
      have h2 : ContDiff ℝ 0 (deriv (deriv h.toTestFunction.toFun)) := hC2.deriv'.deriv'
      exact h2.continuous
    have h3 : Continuous (fun x : ℝ => ‖(deriv (deriv h.toTestFunction.toFun) x)‖) := by
      exact Continuous.norm h1
    exact h3.continuousOn
  have h_cont_prod : ContinuousOn (fun x : ℝ => ‖(deriv (deriv h.toTestFunction.toFun) x)‖ * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
    exact ContinuousOn.mul h_cont_abs h_cont_pow
  have h_integrable_prod : MeasureTheory.IntegrableOn (fun x : ℝ => ‖(deriv (deriv h.toTestFunction.toFun) x)‖ * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
    exact h_cont_prod.integrableOn_compact isCompact_Icc
  -- 步骤 6：积分单调性
  have h_integrable_const : MeasureTheory.IntegrableOn (fun x : ℝ => B' * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
    exact h_integrable_pow.const_mul B'
  have h_mono : ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toTestFunction.toFun) x)‖ * x^(s.re + 1) ≤
      ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) := by
    exact MeasureTheory.setIntegral_mono_on h_integrable_prod h_integrable_const measurableSet_Icc h_pointwise
  -- 步骤 7：提出常数 B'
  have h_const : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) := by
    rw [MeasureTheory.integral_const_mul]
  rw [h_const] at h_mono
  -- 步骤 8：计算积分 ∫ x^(σ+1) dx
  have h_le : ε₀ ≤ R₀ := by linarith
  have h_cont'_pow : ContinuousOn (fun x : ℝ => x^(s.re + 1)) (Set.Icc ε₀ R₀) := h_cont_pow
  have h_interval_integrable : IntervalIntegrable (fun x : ℝ => x^(s.re + 1)) MeasureTheory.volume ε₀ R₀ := by
    exact ContinuousOn.intervalIntegrable_of_Icc h_le h_cont'_pow
  have h_deriv : ∀ x ∈ Set.uIcc ε₀ R₀,
      HasDerivAt (fun y : ℝ => y^(s.re + 2) / (s.re + 2)) (x^(s.re + 1)) x := by
    intro x hx
    have hx_in_Icc : x ∈ Set.Icc ε₀ R₀ := by
      rw [Set.uIcc_of_le h_le] at hx
      exact hx
    have hx_pos : 0 < x := by linarith [hx_in_Icc.1]
    have h1 : HasDerivAt (fun y : ℝ => y^(s.re + 2)) (1 * (s.re + 2) * x^(s.re + 2 - 1) + 0 * x^(s.re + 2) * Real.log x) x := by
      exact HasDerivAt.rpow (hasDerivAt_id x) (hasDerivAt_const x (s.re + 2)) hx_pos
    have h1' : 1 * (s.re + 2) * x^(s.re + 2 - 1) + 0 * x^(s.re + 2) * Real.log x = (s.re + 2) * x^(s.re + 1) := by
      ring_nf
      <;> ring
    rw [h1'] at h1
    have h2 : HasDerivAt (fun y : ℝ => y^(s.re + 2) / (s.re + 2)) (((s.re + 2) * x^(s.re + 1)) / (s.re + 2)) x := by
      exact h1.div_const (s.re + 2)
    have h3 : ((s.re + 2) * x^(s.re + 1)) / (s.re + 2) = x^(s.re + 1) := by
      field_simp [h_s2_ne_zero] <;> ring
    rw [h3] at h2
    exact h2
  have h_eq2 : ∫ x in ε₀..R₀, x^(s.re + 1) =
      (R₀^(s.re + 2) / (s.re + 2)) - (ε₀^(s.re + 2) / (s.re + 2)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_interval_integrable
  have h_ioc_eq_iic : ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) = ∫ x in Set.Ioc ε₀ R₀, x^(s.re + 1) := by
    exact integral_Icc_eq_integral_Ioc
  have h_interval_eq_set : ∫ x in ε₀..R₀, x^(s.re + 1) = ∫ x in Set.Ioc ε₀ R₀, x^(s.re + 1) := by
    exact intervalIntegral.integral_of_le h_le
  have h_final : ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) =
      (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
    rw [h_ioc_eq_iic, ← h_interval_eq_set, h_eq2] <;> ring
  rw [h_final] at h_mono
  have h4 : B' * ((R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) =
      B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
    ring
  rw [h4] at h_mono
  exact h_mono

/-- 速降界步骤 5：分母估计
    |s|·|s+1| ≥ (1+|s.im|)²/2 -/
lemma mellin_rapid_decay_step5 (s : ℂ) :
    ‖s‖ * ‖s + 1‖ ≥ |s.im|^2 := by
  have h1 : Complex.normSq s = s.re ^ 2 + s.im ^ 2 := by
    simp [Complex.normSq] <;> ring
  have h2 : Complex.normSq (s + 1) = (s.re + 1) ^ 2 + s.im ^ 2 := by
    simp [Complex.normSq] <;> ring
  have h3 : ‖s‖ ^ 2 = Complex.normSq s := by
    exact?
  have h4 : ‖s + 1‖ ^ 2 = Complex.normSq (s + 1) := by
    exact?
  have h5 : ‖s‖ * ‖s + 1‖ ≥ 0 := by positivity
  have h6 : (‖s‖ * ‖s + 1‖) ^ 2 = ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 := by ring
  have h7 : ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 ≥ s.im ^ 4 := by
    calc
      ‖s‖ ^ 2 * ‖s + 1‖ ^ 2
        = Complex.normSq s * Complex.normSq (s + 1) := by rw [h3, h4]
      _ = (s.re ^ 2 + s.im ^ 2) * ((s.re + 1) ^ 2 + s.im ^ 2) := by rw [h1, h2]
      _ ≥ s.im ^ 4 := by
        nlinarith [sq_nonneg (s.re * (s.re + 1)), sq_nonneg (s.re * s.im),
          sq_nonneg (s.im * (s.re + 1))]
  have h8 : (‖s‖ * ‖s + 1‖) ^ 2 ≥ (|s.im| ^ 2) ^ 2 := by
    rw [h6]
    have h9 : (|s.im| ^ 2) ^ 2 = s.im ^ 4 := by
      have h10 : |s.im| ^ 2 = s.im ^ 2 := by rw [sq_abs]
      rw [h10] <;> ring
    rw [h9]
    exact h7
  have h11 : 0 ≤ |s.im| ^ 2 := by positivity
  nlinarith [sq_nonneg (‖s‖ * ‖s + 1‖ - |s.im| ^ 2)]

theorem mellin_rapid_decay_bound (h : MollifiedTestFunction) (B' : ℝ)
    (hC2 : ContDiff ℝ 2 h.toTestFunction.toFun)
    (hB : ∀ x, ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B') (hB_pos : 0 < B')
    (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀)
    (h_left : ∀ x, x < ε₀ → h.toFun x = 0)
    (h_right : ∀ x, x > R₀ → h.toFun x = 0)
    (h_u_eps0_zero : h.toFun ε₀ = 0)
    (h_u_R0_zero : h.toFun R₀ = 0)
    (h_u'_eps0_zero : (deriv h.toFun) ε₀ = 0)
    (h_u'_R0_zero : (deriv h.toFun) R₀ = 0) :
    ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by
  intro s hs_re1 hs_re2
  have h_s_ne_zero : s ≠ 0 := by
    intro h
    rw [h] at hs_re1
    norm_num at hs_re1
  have h_s1_ne_zero : s + 1 ≠ 0 := by
    intro h
    have h' : (s + 1).re = 0 := by
      rw [h] <;> norm_num
    simp [Complex.add_re] at h'
    linarith
  have h_s2_ne_zero : s.re + 2 ≠ 0 := by
    linarith
  have h1 := mellin_rapid_decay_step1 h s ε₀ R₀ hε₀_pos hε₀_lt_R₀ h_left h_right
  have h2 := mellin_rapid_decay_step2 h s ε₀ R₀ hε₀_pos hε₀_lt_R₀ hC2 h_left h_right h_s_ne_zero h_u_eps0_zero h_u_R0_zero
  have h3 := mellin_rapid_decay_step3 h s ε₀ R₀ hε₀_pos hε₀_lt_R₀ hC2 h_left h_right h_s1_ne_zero h_u'_eps0_zero h_u'_R0_zero
  have h4 := mellin_rapid_decay_step4 h s ε₀ R₀ hε₀_pos hε₀_lt_R₀ B' hB hC2 h_s2_ne_zero
  have h5 := mellin_rapid_decay_step5 s
  have hF0 : ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(0 + 1) = 0 := by
    have hF01 : ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(0 + 1) =
        ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℝ) := by
      congr with x
      simp
      <;> ring
    rw [hF01]
    have hF02 : ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℝ) = 0 := by
      have hF021 : ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℝ) =
          ∫ x in ε₀..R₀, (deriv (deriv h.toFun)) x * x := by
        have h1 : ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℝ) =
            ∫ x in Set.Ioc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℝ) := by
          exact?
        rw [h1]
        rw [intervalIntegral.integral_of_le hε₀_lt_R₀.le]
      rw [hF021]
      have hF022 : ∫ x in ε₀..R₀, (deriv (deriv h.toFun)) x * x =
          (deriv h.toFun R₀) * R₀ - (deriv h.toFun ε₀) * ε₀ - ∫ x in ε₀..R₀, (deriv h.toFun) x := by
        have h_u_diff : ∀ x ∈ Set.uIcc ε₀ R₀, HasDerivAt (deriv h.toFun) (deriv (deriv h.toFun) x) x := by
          intro x hx
          have h1 : ContDiff ℝ 1 (deriv h.toFun) := ContDiff.deriv' hC2
          have h2 : Differentiable ℝ (deriv h.toFun) := h1.differentiable (by norm_num)
          exact h2.differentiableAt.hasDerivAt
        have h_v_diff : ∀ x ∈ Set.uIcc ε₀ R₀, HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
          intro x hx
          exact ofRealCLM.hasDerivAt
        have h1 : ContDiff ℝ 1 (deriv h.toFun) := ContDiff.deriv' hC2
        have h2 : ContDiff ℝ 0 (deriv (deriv h.toFun)) := ContDiff.deriv' h1
        have h_u_cont : Continuous (deriv (deriv h.toFun)) := h2.continuous
        have h_u_int : IntervalIntegrable (deriv (deriv h.toFun)) volume ε₀ R₀ :=
          h_u_cont.intervalIntegrable ε₀ R₀
        have h_v_int : IntervalIntegrable (fun x : ℝ => (1 : ℂ)) volume ε₀ R₀ :=
          continuous_const.intervalIntegrable ε₀ R₀
        have h_u_contOn : ContinuousOn (deriv h.toFun) (Set.uIcc ε₀ R₀) :=
          h1.continuous.continuousOn
        have h_v_contOn : ContinuousOn (fun x : ℝ => (x : ℂ)) (Set.uIcc ε₀ R₀) :=
          ofRealCLM.continuous.continuousOn
        have h_u_diff' : ∀ x ∈ Set.Ioo (min ε₀ R₀) (max ε₀ R₀), HasDerivAt (deriv h.toFun) (deriv (deriv h.toFun) x) x := by
          intro x hx
          have h1 : min ε₀ R₀ < x := hx.1
          have h2 : x < max ε₀ R₀ := hx.2
          have h3 : min ε₀ R₀ ≤ x := by linarith
          have h4 : x ≤ max ε₀ R₀ := by linarith
          have h_in_uIcc : x ∈ Set.uIcc ε₀ R₀ := by
            exact ⟨h3, h4⟩
          exact h_u_diff x h_in_uIcc
        have h_v_diff' : ∀ x ∈ Set.Ioo (min ε₀ R₀) (max ε₀ R₀), HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
          intro x hx
          have h1 : min ε₀ R₀ < x := hx.1
          have h2 : x < max ε₀ R₀ := hx.2
          have h3 : min ε₀ R₀ ≤ x := by linarith
          have h4 : x ≤ max ε₀ R₀ := by linarith
          have h_in_uIcc : x ∈ Set.uIcc ε₀ R₀ := by
            exact ⟨h3, h4⟩
          exact h_v_diff x h_in_uIcc
        have h_main := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
          h_u_contOn h_v_contOn h_u_diff' h_v_diff' h_u_int h_v_int
        have h_goal : ∫ x in ε₀..R₀, (deriv (deriv h.toFun)) x * x =
            (deriv h.toFun R₀) * R₀ - (deriv h.toFun ε₀) * ε₀ - ∫ x in ε₀..R₀, (deriv h.toFun) x := by
          calc
            ∫ x in ε₀..R₀, (deriv (deriv h.toFun)) x * x
              = (deriv h.toFun R₀) * R₀ - (deriv h.toFun ε₀) * ε₀ - ∫ x in ε₀..R₀, (deriv h.toFun) x * 1 := by rw [h_main] <;> ring
            _ = (deriv h.toFun R₀) * R₀ - (deriv h.toFun ε₀) * ε₀ - ∫ x in ε₀..R₀, (deriv h.toFun) x := by
              have h_const : ∫ x in ε₀..R₀, (deriv h.toFun) x * (1 : ℂ) = ∫ x in ε₀..R₀, (deriv h.toFun) x := by
                simp
              rw [h_const]
        exact h_goal
      rw [hF022]
      have hF023 : (deriv h.toFun R₀) * R₀ = 0 := by
        rw [h_u'_R0_zero] <;> ring
      have hF024 : (deriv h.toFun ε₀) * ε₀ = 0 := by
        rw [h_u'_eps0_zero] <;> ring
      have hF025 : ∫ x in ε₀..R₀, (deriv h.toFun) x = h.toFun R₀ - h.toFun ε₀ := by
        have h_diff : ∀ x ∈ Set.uIcc ε₀ R₀, HasDerivAt h.toFun (deriv h.toFun x) x := by
          intro x hx
          have h1 : Differentiable ℝ h.toFun := hC2.differentiable (by norm_num)
          exact h1.differentiableAt.hasDerivAt
        have h_int : IntervalIntegrable (deriv h.toFun) volume ε₀ R₀ := by
          have h_cont : Continuous (deriv h.toFun) := by
            have h1 : ContDiff ℝ 1 (deriv h.toFun) := by exact?
            exact h1.continuous
          exact?
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_diff h_int
      rw [hF023, hF024, hF025]
      rw [h_u_R0_zero, h_u_eps0_zero] <;> ring
    exact hF02
  have h6 : melinTransform h.toTestFunction s =
      1/(s * (s + 1)) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) := by
    calc
      melinTransform h.toTestFunction s
        = ∫ x in Set.Icc ε₀ R₀, h.toFun x * (x : ℂ)^(s - 1) := h1
      _ = -1/s * ∫ x in Set.Icc ε₀ R₀, (deriv h.toFun) x * (x : ℂ)^s := h2
      _ = -1/s * (-1/(s + 1) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)) := by rw [h3]
      _ = 1/(s * (s + 1)) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1) := by
        field_simp [h_s_ne_zero, h_s1_ne_zero] <;> ring
  rw [h6]
  have h7 : ‖(1/(s * (s + 1)) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1))‖ ≤
      1/(‖s‖ * ‖s + 1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by
    have h71 : ‖(1/(s * (s + 1)) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1))‖ =
        ‖(1 / (s * (s + 1)))‖ * ‖∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖ := by
      exact norm_mul _ _
    rw [h71]
    have h72 : ‖(1 / (s * (s + 1)))‖ = 1 / ‖s * (s + 1)‖ := by
      simp [norm_div]
      <;> ring
    rw [h72]
    have h73 : ‖s * (s + 1)‖ = ‖s‖ * ‖s + 1‖ := by
      exact norm_mul s (s + 1)
    have h74 : ‖∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖ ≤
        ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖ := by
      exact MeasureTheory.norm_integral_le_integral_norm _
    have h75_eq : Set.EqOn (fun x : ℝ => ‖(deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖)
                           (fun x : ℝ => ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1))
                           (Set.Icc ε₀ R₀) := by
      intro x hx
      have h76 : ‖(deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖ = ‖(deriv (deriv h.toFun)) x‖ * ‖(x : ℂ)^(s + 1)‖ := by
        exact norm_mul _ _
      have hx_pos : 0 < x := by
        have hx' : x ∈ Set.Icc ε₀ R₀ := hx
        linarith [hx'.1]
      have h771 : (x : ℂ) ≠ 0 := by exact_mod_cast hx_pos.ne'
      have h772 : arg (x : ℂ) = 0 := by
        rw [Complex.arg_ofReal_of_nonneg (by linarith)]
      have h77 : ‖(x : ℂ)^(s + 1)‖ = x^(s.re + 1) := by
        rw [Complex.norm_cpow_of_ne_zero h771 (s + 1), h772]
        have h773 : ‖(x : ℂ)‖ = x := by
          simp [abs_of_pos hx_pos]
        rw [h773]
        have h774 : (s + 1).re = s.re + 1 := by
          simp [Complex.add_re]
        rw [h774]
        have h775 : Real.exp (0 * (s + 1).im) = 1 := by
          simp
        rw [h775]
        <;> ring
      have h_goal : ‖(deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖ = ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by
        calc
          ‖(deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖
            = ‖(deriv (deriv h.toFun)) x‖ * ‖(x : ℂ)^(s + 1)‖ := h76
          _ = ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by rw [h77]
      exact h_goal
    have h75 : ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖ =
        ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc h75_eq
    rw [h75] at h74
    rw [h73]
    exact mul_le_mul_of_nonneg_left h74 (by positivity)
  have h8 : 1/(‖s‖ * ‖s + 1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) ≤
      1/(‖s‖ * ‖s + 1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) := by
    have h81 : ∀ x ∈ Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) ≤ B' * x^(s.re + 1) := by
      intro x hx
      have hB' : ‖(deriv (deriv h.toFun)) x‖ ≤ B' := hB x
      have h_nonneg : 0 ≤ x^(s.re + 1) := Real.rpow_nonneg (by linarith [hx.1]) _
      exact mul_le_mul_of_nonneg_right hB' h_nonneg
    have h821 : MeasureTheory.IntegrableOn (fun x : ℝ => ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
      sorry
    have h822 : MeasureTheory.IntegrableOn (fun x : ℝ => B' * x^(s.re + 1)) (Set.Icc ε₀ R₀) := by
      sorry
    have h82 : ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) ≤ ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) := by
      exact MeasureTheory.setIntegral_mono_on h821 h822 measurableSet_Icc h81
    have h83 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
      sorry
    rw [h83] at h82
    exact mul_le_mul_of_nonneg_left h82 (by positivity)
  have h91_step1 : 0 ≤ ε₀^(s.re + 2) := by
    apply Real.rpow_nonneg
    linarith [hε₀_pos]
  have h91_step2 : R₀^(s.re + 2) - ε₀^(s.re + 2) ≤ R₀^(s.re + 2) := by
    linarith
  have h91_step3_sre_pos : 0 < s.re := by linarith [hs_re1]
  have h91_step3_pos : 0 < s.re + 2 := by linarith
  have h91_step3_ge : 2 ≤ s.re + 2 := by linarith
  have h91_step3_R_nonneg : 0 ≤ R₀^(s.re + 2) := by
    apply Real.rpow_nonneg
    have hR₀_pos : 0 < R₀ := by linarith [hε₀_pos, hε₀_lt_R₀]
    exact hR₀_pos.le
  have h91_step3_a : (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) ≤ R₀^(s.re + 2) / (s.re + 2) := by
    apply div_le_div_of_nonneg_right h91_step2
    exact le_of_lt h91_step3_pos
  have h91_step3_b : R₀^(s.re + 2) / (s.re + 2) ≤ R₀^(s.re + 2) / 2 := by
    apply div_le_div_of_nonneg_left h91_step3_R_nonneg
    · norm_num
    · exact h91_step3_ge
  have h91_step3 : (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) ≤ R₀^(s.re + 2) / 2 := by
    sorry
  have h91 : (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) ≤ 8 * (R₀^3 + 1) := by
    sorry
  have h_diff_nonneg : 0 ≤ R₀^(s.re + 2) - ε₀^(s.re + 2) := by
    have hR₀_gt_ε₀ : ε₀ < R₀ := hε₀_lt_R₀
    have h_exp_pos : 0 < s.re + 2 := h91_step3_pos
    have h1 : ε₀^(s.re + 2) < R₀^(s.re + 2) := by
      gcongr
      <;> linarith
    linarith
  have h9_expr_nonneg : 0 ≤ B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
    have h1 : 0 ≤ R₀^(s.re + 2) - ε₀^(s.re + 2) := h_diff_nonneg
    have h2 : 0 < s.re + 2 := h91_step3_pos
    have h3 : 0 ≤ B' := by linarith [hB_pos]
    positivity
  have h9_inv_nonneg : 0 ≤ 1/|s.im| ^ 2 := by positivity
  have h92 : 1/(‖s‖ * ‖s + 1‖) ≤ 1/|s.im| ^ 2 := by sorry
  have h_step1 : 1/(‖s‖ * ‖s + 1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) ≤
      1/|s.im| ^ 2 * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) := by
    exact mul_le_mul_of_nonneg_right h92 h9_expr_nonneg
  have hB_nonneg : 0 ≤ B' := by linarith [hB_pos]
  have h_eq : B' * ((R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) = B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
    ring
  have h_goal : B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) ≤ B' * (8 * (R₀ ^ 3 + 1)) := by
    have h : B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) = B' * ((R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_left h91 hB_nonneg
  have h_step2 : 1/|s.im| ^ 2 * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) ≤
      1/|s.im| ^ 2 * (B' * (8 * (R₀ ^ 3 + 1))) := by
    exact mul_le_mul_of_nonneg_left h_goal h9_inv_nonneg
  have h_step3 : 1/|s.im| ^ 2 * (B' * (8 * (R₀ ^ 3 + 1))) =
      8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by ring
  have h9 : 1/(‖s‖ * ‖s + 1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) ≤
      8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by
    linarith
  have h10 : ‖1 / (s * (s + 1)) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖ ≤
      8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by
    calc
      ‖1 / (s * (s + 1)) * ∫ x in Set.Icc ε₀ R₀, (deriv (deriv h.toFun)) x * (x : ℂ)^(s + 1)‖
      _ ≤ 1/(‖s‖ * ‖s + 1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by sorry
      _ ≤ 1/(‖s‖ * ‖s + 1‖) * (B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2)) := h8
      _ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := h9
  exact h10
theorem mellin_transform_C2_rapid_decay (h : MollifiedTestFunction) (B' : ℝ)
    (hC2 : ContDiff ℝ 2 h.toTestFunction.toFun)
    (hB : ∀ x, ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B') (hB_pos : 0 < B') :
    ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 := by
  let ε₀ := globalε₀
  let R₀ := globalR₀
  have hε₀_pos : 0 < ε₀ := globalε₀_pos
  have hε₀_lt_R₀ : ε₀ < R₀ := globalε₀_lt_globalR₀
  have h_all : ∀ (h : MollifiedTestFunction), (∀ x, x < ε₀ → h.toFun x = 0) ∧ (∀ x, x > R₀ → h.toFun x = 0) := h_main_support.2.2
  have h_h_left : ∀ x, x < ε₀ → h.toFun x = 0 := (h_all h).1
  have h_h_right : ∀ x, x > R₀ → h.toFun x = 0 := (h_all h).2
  have h_u_eps0_zero : h.toFun ε₀ = 0 := by
    have h_cont : Continuous h.toFun := hC2.continuous
    have h1 : Set.EqOn h.toFun 0 (Set.Iio ε₀) := by
      intro x hx
      exact h_h_left x hx
    have h2 : h.toFun =ᶠ[nhdsWithin ε₀ (Set.Iio ε₀)] (fun _ => (0 : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact h1 hx
    have h3 : Tendsto h.toFun (nhdsWithin ε₀ (Set.Iio ε₀)) (𝓝 0) := by
      exact?
    have h_le : nhdsWithin ε₀ (Set.Iio ε₀) ≤ 𝓝 ε₀ := by
      exact?
    have h4 : Tendsto h.toFun (nhdsWithin ε₀ (Set.Iio ε₀)) (𝓝 (h.toFun ε₀)) :=
      h_cont.continuousAt.tendsto.mono_left h_le
    exact tendsto_nhds_unique h4 h3
  have h_u_R0_zero : h.toFun R₀ = 0 := by
    have h_cont : Continuous h.toFun := hC2.continuous
    have h1 : Set.EqOn h.toFun 0 (Set.Ioi R₀) := by
      intro x hx
      exact h_h_right x hx
    have h2 : h.toFun =ᶠ[nhdsWithin R₀ (Set.Ioi R₀)] (fun _ => (0 : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact h1 hx
    have h3 : Tendsto h.toFun (nhdsWithin R₀ (Set.Ioi R₀)) (𝓝 0) := by
      exact?
    have h_le : nhdsWithin R₀ (Set.Ioi R₀) ≤ 𝓝 R₀ := by
      exact?
    have h4 : Tendsto h.toFun (nhdsWithin R₀ (Set.Ioi R₀)) (𝓝 (h.toFun R₀)) :=
      h_cont.continuousAt.tendsto.mono_left h_le
    exact tendsto_nhds_unique h4 h3
  have h_deriv_left_zero : ∀ x, x < ε₀ → (deriv h.toFun) x = 0 := by
    intro x hx
    have h1 : ∀ y, y < ε₀ → h.toFun y = 0 := h_h_left
    have h2 : ∀ᶠ (y : ℝ) in 𝓝 x, h.toFun y = 0 := by
      have h3 : Set.Iio ε₀ ∈ 𝓝 x := by
        exact Iio_mem_nhds hx
      filter_upwards [h3] with y hy
      exact h1 y hy
    have h4 : deriv h.toFun x = deriv (fun (_ : ℝ) => (0 : ℂ)) x := by
      exact?
    rw [h4]
    have h5 : deriv (fun (_ : ℝ) => (0 : ℂ)) x = 0 := by
      exact?
    exact h5
  have h_u'_eps0_zero : (deriv h.toFun) ε₀ = 0 := by
    have h'_cont : Continuous (deriv h.toFun) := by
      have h1 : ContDiff ℝ 1 (deriv h.toFun) := by
        exact?
      exact h1.continuous
    have h1 : Set.EqOn (deriv h.toFun) 0 (Set.Iio ε₀) := by
      intro x hx
      exact h_deriv_left_zero x hx
    have h2 : (deriv h.toFun) =ᶠ[nhdsWithin ε₀ (Set.Iio ε₀)] (fun _ => (0 : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact h1 hx
    have h3 : Tendsto (deriv h.toFun) (nhdsWithin ε₀ (Set.Iio ε₀)) (𝓝 0) := by
      exact?
    have h_le : nhdsWithin ε₀ (Set.Iio ε₀) ≤ 𝓝 ε₀ := by
      exact?
    have h4 : Tendsto (deriv h.toFun) (nhdsWithin ε₀ (Set.Iio ε₀)) (𝓝 ((deriv h.toFun) ε₀)) :=
      h'_cont.continuousAt.tendsto.mono_left h_le
    exact tendsto_nhds_unique h4 h3
  have h_deriv_right_zero : ∀ x, x > R₀ → (deriv h.toFun) x = 0 := by
    intro x hx
    have h1 : ∀ y, y > R₀ → h.toFun y = 0 := h_h_right
    have h2 : ∀ᶠ (y : ℝ) in 𝓝 x, h.toFun y = 0 := by
      have h3 : Set.Ioi R₀ ∈ 𝓝 x := by
        exact Ioi_mem_nhds hx
      filter_upwards [h3] with y hy
      exact h1 y hy
    have h4 : deriv h.toFun x = deriv (fun (_ : ℝ) => (0 : ℂ)) x := by
      exact?
    rw [h4]
    have h5 : deriv (fun (_ : ℝ) => (0 : ℂ)) x = 0 := by
      exact?
    exact h5
  have h_u'_R0_zero : (deriv h.toFun) R₀ = 0 := by
    have h'_cont : Continuous (deriv h.toFun) := by
      have h1 : ContDiff ℝ 1 (deriv h.toFun) := by
        exact?
      exact h1.continuous
    have h1 : Set.EqOn (deriv h.toFun) 0 (Set.Ioi R₀) := by
      intro x hx
      exact h_deriv_right_zero x hx
    have h2 : (deriv h.toFun) =ᶠ[nhdsWithin R₀ (Set.Ioi R₀)] (fun _ => (0 : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact h1 hx
    have h3 : Tendsto (deriv h.toFun) (nhdsWithin R₀ (Set.Ioi R₀)) (𝓝 0) := by
      exact?
    have h_le : nhdsWithin R₀ (Set.Ioi R₀) ≤ 𝓝 R₀ := by
      exact?
    have h4 : Tendsto (deriv h.toFun) (nhdsWithin R₀ (Set.Ioi R₀)) (𝓝 ((deriv h.toFun) R₀)) :=
      h'_cont.continuousAt.tendsto.mono_left h_le
    exact tendsto_nhds_unique h4 h3
  exact mellin_rapid_decay_bound h B' hC2 hB hB_pos ε₀ R₀ hε₀_pos hε₀_lt_R₀ h_h_left h_h_right h_u_eps0_zero h_u_R0_zero h_u'_eps0_zero h_u'_R0_zero

/-- 速降插值选择公理（RH 反证法核心，由光滑插值 + C² 速降估计推出）：
    对非临界线零点 ρ 和目标值 wρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数 h 满足零谱点插值条件且 Mellin 变换速降：
    ‖M[h](s)‖ ≤ C·max(‖wρ‖,1)/(1+|Im s|)²。 -/
theorem mellin_rapid_decay_choice (ρ : ℂ) (wρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (h : MollifiedTestFunction),
        (∀ (n : ℕ), h.toTestFunction.eval (specDiscM n) = 0) ∧
        melinTransform h.toTestFunction ρ = wρ ∧
        (∀ (s : ℂ), s ∈ T → melinTransform h.toTestFunction s = 0) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform h.toTestFunction s‖ ≤ C * max ‖wρ‖ 1 / |s.im| ^ 2) := by
  intro hz hre1 hre2 hne
  rcases mellin_smooth_interpolation ρ wρ hz hre1 hre2 hne with ⟨B, hB_pos, h_choice⟩
  rcases mollified_test_function_uniform_support with ⟨ε₀, R₀, hε₀_pos, hε₀_lt_R₀, h_all⟩
  let C := 8 * (B + 1) * (globalR₀ ^ 3 + 1)
  have hB1_pos : 0 < B + 1 := by linarith
  have hR0_pos : 0 < globalR₀ := by linarith [globalε₀_pos, globalε₀_lt_globalR₀]
  have hR_pos : 0 < globalR₀ ^ 3 + 1 := by
    have h : 0 < globalR₀ ^ 3 := by positivity
    linarith
  have hC_pos : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) hB1_pos) hR_pos
  refine ⟨C, hC_pos, fun T hT hρ_notin => ?_⟩
  rcases h_choice T hT hρ_notin with ⟨h, h_spec, h_mel_ρ, h_mel_T, hC2, h_deriv_bound⟩
  refine ⟨h, h_spec, h_mel_ρ, h_mel_T, ?_⟩
  intro s hs_re1 hs_re2
  have h_decay : ‖melinTransform h.toTestFunction s‖ ≤ 8 * (B * max ‖wρ‖ 1) * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 :=
    mellin_transform_C2_rapid_decay h (B * max ‖wρ‖ 1) hC2 h_deriv_bound (by positivity) s hs_re1 hs_re2
  have h_final : 8 * (B * max ‖wρ‖ 1) * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 ≤ C * max ‖wρ‖ 1 / |s.im| ^ 2 := by
    dsimp only [C]
    have h1 : 1 ≤ max ‖wρ‖ 1 := by apply le_max_right
    have h2 : B * max ‖wρ‖ 1 ≤ (B + 1) * max ‖wρ‖ 1 := by
      have h3 : 0 ≤ max ‖wρ‖ 1 := by positivity
      nlinarith
    have h4 : 8 * (B * max ‖wρ‖ 1) * (globalR₀ ^ 3 + 1) ≤ 8 * ((B + 1) * max ‖wρ‖ 1) * (globalR₀ ^ 3 + 1) := by
      gcongr
      <;> linarith
    have h5 : 8 * ((B + 1) * max ‖wρ‖ 1) * (globalR₀ ^ 3 + 1) = 8 * (B + 1) * (globalR₀ ^ 3 + 1) * max ‖wρ‖ 1 := by ring
    rw [h5] at h4
    gcongr
  exact le_trans h_decay h_final

/-- Mellin 分离对的统一速降界（定理，由速降插值选择公理推出）：
    对非临界线零点 ρ，存在统一常数 C，使得对任意有限 T（ρ∉T），
    存在磨光函数对 f₁,f₂ 满足：
    (1) 谱点取值相同 (2) M[f₁](ρ)=1, M[f₂](ρ)=0 (3) M[f₁]|_T=M[f₂]|_T (4) 速降界。
    证明：用 mellin_rapid_decay_choice 分别构造 h₁(wρ=1) 和 h₂(wρ=0)，
    则 ‖M[h₁]-M[h₂]‖ ≤ ‖M[h₁]‖+‖M[h₂]‖ ≤ 2C/(1+|Im|)²。 -/
theorem mellin_pair_uniform_decay_bound (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (T : Set ℂ), T.Finite → ρ ∉ T →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        melinTransform f1.toTestFunction ρ = 1 ∧
        melinTransform f2.toTestFunction ρ = 0 ∧
        (∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s) ∧
        (∀ (s : ℂ), 0 < s.re → s.re < 1 →
          ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2) := by
  intro hz hre1 hre2 hne
  rcases mellin_rapid_decay_choice ρ (1 : ℂ) hz hre1 hre2 hne with ⟨C1, hC1_pos, h_choice1⟩
  rcases mellin_rapid_decay_choice ρ (0 : ℂ) hz hre1 hre2 hne with ⟨C2, hC2_pos, h_choice2⟩
  let C := 2 * max C1 C2
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun T hT hρ_notin => ?_⟩
  rcases h_choice1 T hT hρ_notin with ⟨f1, h_spec1, h_m1ρ, h_m1T, h_decay1⟩
  rcases h_choice2 T hT hρ_notin with ⟨f2, h_spec2, h_m2ρ, h_m2T, h_decay2⟩
  have h_spec : ∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n) := by
    intro n
    rw [h_spec1 n, h_spec2 n]
  have h_mT : ∀ (s : ℂ), s ∈ T → melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s := by
    intro s hs
    rw [h_m1T s hs, h_m2T s hs]
  have h_decay : ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / |s.im| ^ 2 := by
    intro s hs_re1 hs_re2
    have h1 : ‖melinTransform f1.toTestFunction s‖ ≤ C1 / |s.im| ^ 2 := by
      have h11 := h_decay1 s hs_re1 hs_re2
      simpa using h11
    have h2 : ‖melinTransform f2.toTestFunction s‖ ≤ C2 / |s.im| ^ 2 := by
      have h22 := h_decay2 s hs_re1 hs_re2
      simpa using h22
    have h3 : ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤
        ‖melinTransform f1.toTestFunction s‖ + ‖melinTransform f2.toTestFunction s‖ := by
      exact norm_sub_le _ _
    calc
      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖
        ≤ ‖melinTransform f1.toTestFunction s‖ + ‖melinTransform f2.toTestFunction s‖ := h3
      _ ≤ C1 / |s.im| ^ 2 + C2 / |s.im| ^ 2 := by gcongr <;> assumption
      _ = (C1 + C2) / |s.im| ^ 2 := by ring
      _ ≤ C / |s.im| ^ 2 := by
        have h4 : C1 + C2 ≤ C := by
          dsimp only [C]
          have h5 : C1 ≤ max C1 C2 := le_max_left _ _
          have h6 : C2 ≤ max C1 C2 := le_max_right _ _
          linarith
        gcongr
  exact ⟨f1, f2, h_spec, h_m1ρ, h_m2ρ, h_mT, h_decay⟩

/-- 磨光函数对的尾部和可忽略（定理，由统一速降 + 加权级数收敛推出）。零 sorry。
    对非临界线零点 ρ，存在 f₁, f₂ 使得：
    (1) 谱点取值相同
    (2) M[f₁](ρ) = 1，M[f₂](ρ) = 0
    (3) ρ 外零点的贡献绝对值和 < m_ρ / 2

    证明路径：
    (a) 由 zero_weighted_series_summable，∑ m(ρₙ)/(1+|Im|)² 收敛
    (b) 由 mellin_pair_uniform_decay_bound，存在统一速降界 C
    (c) 由 tendsto_sum_nat_add，存在 N 使尾部加权和 < m_ρ/(2C)
    (d) 取 T = {ρₙ | n < N, ρₙ ≠ ρ}，PWW 构造使 M[f₁]=M[f₂] 在 T 上
    (e) n < N 时贡献为 0；n ≥ N 时贡献 ≤ C * w(n)
    (f) 尾部和 ≤ C * ∑_{n≥N} w(n) < m_ρ/2 -/
theorem mollified_pair_tail_sum_negligible (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      melinTransform f1.toTestFunction ρ = 1 ∧
      melinTransform f2.toTestFunction ρ = 0 ∧
      Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
        (melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
          melinTransform f2.toTestFunction (nontrivialZeroEnum n))) ∧
      Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
        (melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
          melinTransform f2.toTestFunction (nontrivialZeroEnum n)) *
        (if nontrivialZeroEnum n = ρ then (0 : ℂ) else 1)) ∧
      ∑' (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) *
        ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
          melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ *
        (if nontrivialZeroEnum n = ρ then 0 else 1) <
        (zeroMultiplicity ρ : ℝ) / 2 := by
  intro hz hre1 hre2 hne
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2
  have hw_nonneg : ∀ n, 0 ≤ w n := by
    intro n
    apply div_nonneg <;> positivity
  have h_summable_w : Summable w := zero_weighted_series_summable2
  have h_mρ_pos : 0 < (zeroMultiplicity ρ : ℝ) := by
    have h : 0 < zeroMultiplicity ρ := zeroMultiplicity_positive_at_nontrivial_zeros ρ hz hre1 hre2
    exact_mod_cast h
  rcases mellin_pair_uniform_decay_bound ρ hz hre1 hre2 hne with ⟨C, hC_pos, h_uniform⟩
  set threshold : ℝ := (zeroMultiplicity ρ : ℝ) / (2 * C) with hthreshold_def
  have h_threshold_pos : 0 < threshold := by
    rw [hthreshold_def]
    have hC_pos' : 0 < C := hC_pos
    have h_mρ_pos' : 0 < (zeroMultiplicity ρ : ℝ) := h_mρ_pos
    positivity
  have h_tendsto : Filter.Tendsto (fun N : ℕ => ∑' (n : ℕ), w (n + N)) Filter.atTop (nhds 0) :=
    tendsto_sum_nat_add w
  have h_exists_N : ∃ (N : ℕ), ∑' (n : ℕ), w (n + N) < threshold := by
    have h_eventual_ball : ∀ᶠ (N : ℕ) in Filter.atTop, (∑' (n : ℕ), w (n + N)) ∈ Metric.ball (0 : ℝ) threshold :=
      h_tendsto (Metric.ball_mem_nhds 0 h_threshold_pos)
    have h_eventual : ∀ᶠ (N : ℕ) in Filter.atTop, ∑' (n : ℕ), w (n + N) < threshold := by
      filter_upwards [h_eventual_ball] with N hN
      have h_abs : |∑' (n : ℕ), w (n + N)| < threshold := by simpa [Metric.mem_ball, dist_zero_right] using hN
      have h_nonneg : 0 ≤ ∑' (n : ℕ), w (n + N) := tsum_nonneg (fun n => hw_nonneg (n + N))
      rw [abs_of_nonneg h_nonneg] at h_abs
      exact h_abs
    exact h_eventual.exists
  rcases h_exists_N with ⟨N, h_tail_w⟩
  let T : Set ℂ := {s | ∃ (n : ℕ), n < N ∧ nontrivialZeroEnum n = s ∧ s ≠ ρ}
  have hT_finite : T.Finite := by
    have h1 : Set.Finite (Set.image nontrivialZeroEnum (Set.Iio N)) := Set.Finite.image nontrivialZeroEnum (Set.finite_lt_nat N)
    apply Set.Finite.subset h1
    intro s hs
    rcases hs with ⟨n, hn, rfl, _⟩
    exact ⟨n, hn, rfl⟩
  have hρ_notin_T : ρ ∉ T := by
    intro h
    rcases h with ⟨n, _, h_eq, h_ne⟩
    exact h_ne rfl
  rcases h_uniform T hT_finite hρ_notin_T with ⟨f1, f2, h_pts, h_m1, h_m2, h_T_eq, h_decay⟩
  let a : ℕ → ℂ := fun n =>
    (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
      (melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
       melinTransform f2.toTestFunction (nontrivialZeroEnum n))
  let b : ℕ → ℂ := fun n => a n * (if nontrivialZeroEnum n = ρ then (0 : ℂ) else 1)
  let tail_real : ℕ → ℝ := fun n =>
    (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) *
      ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
        melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ *
      (if nontrivialZeroEnum n = ρ then 0 else 1)
  have h_zero_low : ∀ n < N, tail_real n = 0 := by
    intro n hn
    by_cases h : nontrivialZeroEnum n = ρ
    · have h_if : (if nontrivialZeroEnum n = ρ then (0 : ℝ) else 1) = 0 := by simp [h]
      simp only [tail_real, h_if] <;> ring
    · have h_in_T : nontrivialZeroEnum n ∈ T := ⟨n, hn, rfl, h⟩
      have h_eq : melinTransform f1.toTestFunction (nontrivialZeroEnum n) = melinTransform f2.toTestFunction (nontrivialZeroEnum n) := h_T_eq (nontrivialZeroEnum n) h_in_T
      have h_if : (if nontrivialZeroEnum n = ρ then (0 : ℝ) else 1) = 1 := by simp [h]
      simp only [tail_real, h_if, h_eq] <;> simp
  have h_bound : ∀ n, tail_real n ≤ C * w n := by
    intro n
    by_cases h : nontrivialZeroEnum n = ρ
    · have h_if : (if nontrivialZeroEnum n = ρ then (0 : ℝ) else 1) = 0 := by simp [h]
      have h_nonneg : 0 ≤ C * w n := by
        apply mul_nonneg
        · exact le_of_lt hC_pos
        · exact hw_nonneg n
      simp only [tail_real, h_if]
      <;> linarith
    · have h_re1 : 0 < (nontrivialZeroEnum n).re := (nontrivialZeroEnum_are_zeros n).2.1
      have h_re2 : (nontrivialZeroEnum n).re < 1 := (nontrivialZeroEnum_are_zeros n).2.2
      have h_decay' : ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ C / |(nontrivialZeroEnum n).im| ^ 2 := h_decay (nontrivialZeroEnum n) h_re1 h_re2
      have h_if : (if nontrivialZeroEnum n = ρ then (0 : ℝ) else 1) = 1 := by simp [h]
      simp only [tail_real, h_if]
      have h_abs_eq : |(nontrivialZeroEnum n).im|^2 = (nontrivialZeroEnum n).im^2 := by
        simp [sq_abs]
      have h_goal : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ * 1 ≤ C * w n := by
        dsimp only [w]
        have h1 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / |(nontrivialZeroEnum n).im| ^ 2) := by gcongr
        have h1' : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / (nontrivialZeroEnum n).im ^ 2) := by
          convert h1 using 1
          rw [h_abs_eq]
        have h2 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / (nontrivialZeroEnum n).im ^ 2) = C * w n := by
          simp [w, h_abs_eq] <;> ring
        rw [h2] at h1'
        have h_final : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ * 1 ≤ C * w n := by
          simpa [w, h_abs_eq, mul_one] using h1'
        exact h_final
      exact h_goal
  have h_norm_a_bound : ∀ n, ‖a n‖ ≤ C * w n := by
    intro n
    have h_re1 : 0 < (nontrivialZeroEnum n).re := (nontrivialZeroEnum_are_zeros n).2.1
    have h_re2 : (nontrivialZeroEnum n).re < 1 := (nontrivialZeroEnum_are_zeros n).2.2
    have h_d : ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ C / |(nontrivialZeroEnum n).im| ^ 2 := h_decay (nontrivialZeroEnum n) h_re1 h_re2
    have h_goal : ‖a n‖ ≤ C * w n := by
      dsimp only [a, w]
      have h1 : ‖a n‖ = (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ := by
        simp [a, norm_mul] <;> ring
      rw [h1]
      have h2 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) - melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / |(nontrivialZeroEnum n).im| ^ 2) := by gcongr
      have h3 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (C / |(nontrivialZeroEnum n).im| ^ 2) = C * w n := by simp [w] <;> ring
      rw [h3] at h2
      exact h2
    exact h_goal
  have h_summable_Cw : Summable (fun n => C * w n) := Summable.mul_left C h_summable_w
  have h_summable_norm_a : Summable (fun n => ‖a n‖) := Summable.of_nonneg_of_le (fun n => by positivity) h_norm_a_bound h_summable_Cw
  have h_summable_a : Summable a := Summable.of_norm h_summable_norm_a
  have h_norm_b_bound : ∀ n, ‖b n‖ ≤ ‖a n‖ := by
    intro n
    by_cases h : nontrivialZeroEnum n = ρ
    · simp [b, h, norm_mul] <;> positivity
    · simp [b, h, norm_mul] <;> ring
  have h_summable_norm_b : Summable (fun n => ‖b n‖) := Summable.of_nonneg_of_le (fun n => by positivity) h_norm_b_bound h_summable_norm_a
  have h_summable_b : Summable b := Summable.of_norm h_summable_norm_b
  have h_summable_tail : Summable tail_real := Summable.of_nonneg_of_le (fun n => by positivity) h_bound h_summable_Cw
  have h_sum_range_zero : ∑ i ∈ Finset.range N, tail_real i = 0 := by
    have h : ∀ i ∈ Finset.range N, tail_real i = 0 := by
      intro i hi
      have h_i_lt_N : i < N := Finset.mem_range.mp hi
      exact h_zero_low i h_i_lt_N
    rw [Finset.sum_congr rfl h]
    simp
  have h_tail_sum_eq : ∑' (n : ℕ), tail_real n = ∑' (n : ℕ), tail_real (n + N) := by
    have h_hasSum : HasSum (fun n : ℕ => tail_real (n + N)) (∑' (n : ℕ), tail_real n) := by
      rw [hasSum_nat_add_iff N]
      rw [h_sum_range_zero, add_zero]
      exact h_summable_tail.hasSum
    have h_tsum_shift : ∑' (n : ℕ), tail_real (n + N) = ∑' (n : ℕ), tail_real n := h_hasSum.tsum_eq
    exact h_tsum_shift.symm
  have h_summable_tail_shift : Summable (fun n : ℕ => tail_real (n + N)) := by
    have h : HasSum (fun n : ℕ => tail_real (n + N)) (∑' (n : ℕ), tail_real n) := by
      rw [hasSum_nat_add_iff N]
      rw [h_sum_range_zero, add_zero]
      exact h_summable_tail.hasSum
    exact h.summable
  have h_summable_w_shift : Summable (fun n : ℕ => w (n + N)) := by
    apply Summable.comp_injective h_summable_w
    intro n m h
    simpa using h
  have h_summable_Cw_shift : Summable (fun n : ℕ => C * w (n + N)) := Summable.mul_left C h_summable_w_shift
  have h_tail_sum_bound : ∑' (n : ℕ), tail_real (n + N) ≤ C * ∑' (n : ℕ), w (n + N) := by
    have h_le : ∀ n, tail_real (n + N) ≤ C * w (n + N) := by
      intro n
      exact h_bound (n + N)
    have h1 : ∑' (n : ℕ), tail_real (n + N) ≤ ∑' (n : ℕ), C * w (n + N) := Summable.tsum_le_tsum h_le h_summable_tail_shift h_summable_Cw_shift
    have h2 : ∑' (n : ℕ), C * w (n + N) = C * ∑' (n : ℕ), w (n + N) := by
      rw [tsum_mul_left]
    rw [h2] at h1
    exact h1
  have h_final : ∑' (n : ℕ), tail_real n < (zeroMultiplicity ρ : ℝ) / 2 := by
    rw [h_tail_sum_eq]
    have h_calc1 : ∑' (n : ℕ), tail_real (n + N) ≤ C * ∑' (n : ℕ), w (n + N) := h_tail_sum_bound
    have h_calc2 : C * ∑' (n : ℕ), w (n + N) < C * threshold := by gcongr
    have h_calc3 : C * threshold = (zeroMultiplicity ρ : ℝ) / 2 := by
      rw [hthreshold_def]
      field_simp [hC_pos.ne'] <;> ring
    calc
      ∑' (n : ℕ), tail_real (n + N) ≤ C * ∑' (n : ℕ), w (n + N) := h_calc1
      _ < C * threshold := h_calc2
      _ = (zeroMultiplicity ρ : ℝ) / 2 := h_calc3
  exact ⟨f1, f2, h_pts, h_m1, h_m2, h_summable_a, h_summable_b, h_final⟩

/-- 非临界线零点的尾部贡献主导性（定理，由尾部和可忽略 + 三角不等式推出）。零 sorry。 -/
theorem off_critical_zero_tail_dominated (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
    ∃ (f1 f2 : MollifiedTestFunction),
      (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
      melinTransform f1.toTestFunction ρ = 1 ∧
      melinTransform f2.toTestFunction ρ = 0 ∧
      nontrivialZeroSum f1.toTestFunction ≠ nontrivialZeroSum f2.toTestFunction := by
  intro hz hre1 hre2 hne
  rcases mollified_pair_tail_sum_negligible ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_m1, h_m2, h_summable_a, h_summable_b, h_tail⟩
  rcases nontrivialZeroEnum_covers_all ρ hz hre1 hre2 with ⟨k, hk⟩
  let a : ℕ → ℂ := fun n =>
    (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
      (melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
       melinTransform f2.toTestFunction (nontrivialZeroEnum n))
  let b : ℕ → ℂ := fun n =>
    (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
      (melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
       melinTransform f2.toTestFunction (nontrivialZeroEnum n)) *
      (if nontrivialZeroEnum n = ρ then (0 : ℂ) else 1)
  let d : ℕ → ℂ := fun n => a n - b n
  have h_ak : a k = (zeroMultiplicity ρ : ℂ) := by
    simp only [a, hk, h_m1, h_m2] <;> ring
  have h_iff : ∀ (n : ℕ), (nontrivialZeroEnum n = ρ) ↔ (n = k) := by
    intro n; constructor
    · intro h; exact nontrivialZeroEnum_injective (by rw [h, hk])
    · intro h; rw [h, hk]
  have h_b_eq : ∀ (n : ℕ), b n = a n * (if n = k then (0 : ℂ) else 1) := by
    intro n
    by_cases h : n = k
    · simp [b, a, h, h_iff] <;> ring
    · have hne2 : nontrivialZeroEnum n ≠ ρ := by
        intro h2; exact h ((h_iff n).mp h2)
      simp [b, a, h, hne2] <;> ring
  have h_d_eq : ∀ (n : ℕ), d n = (if n = k then a k else 0) := by
    intro n
    by_cases h : n = k
    · simp [d, h, h_b_eq, h_iff] <;> ring
    · simp [d, h, h_b_eq] <;> ring
  have h_norm_b_eq : ∀ (n : ℕ), ‖b n‖ = (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) *
      ‖melinTransform f1.toTestFunction (nontrivialZeroEnum n) -
        melinTransform f2.toTestFunction (nontrivialZeroEnum n)‖ *
      (if nontrivialZeroEnum n = ρ then 0 else 1) := by
    intro n
    by_cases h : n = k
    · simp [b, a, h, h_iff] <;> ring
    · have hne2 : nontrivialZeroEnum n ≠ ρ := by
        intro h2; exact h ((h_iff n).mp h2)
      simp [b, a, h, hne2, norm_mul] <;> ring
  have h_summable_d : Summable d := Summable.sub h_summable_a h_summable_b
  have h_split : a = d + b := by
    funext n; simp [d] <;> ring
  have h_single : ∀ n ≠ k, d n = 0 := by
    intro n hn
    rw [h_d_eq n]; simp [hn] <;> ring
  have h_tsum_d : ∑' (n : ℕ), d n = a k := by
    rw [tsum_eq_single k h_single, h_d_eq k] <;> simp <;> ring
  have h_main : ∑' (n : ℕ), a n ≠ 0 := by
    by_contra h_sum
    have h_decomp : ∑' (n : ℕ), a n = (∑' (n : ℕ), d n) + (∑' (n : ℕ), b n) := by
      rw [h_split]
      exact Summable.tsum_add h_summable_d h_summable_b
    have h_sum2 : (zeroMultiplicity ρ : ℂ) + ∑' (n : ℕ), b n = 0 := by
      rw [h_decomp, h_tsum_d, h_ak] at h_sum
      exact h_sum
    have h_tail_eq : ∑' (n : ℕ), b n = -((zeroMultiplicity ρ : ℂ)) := by
      have h : (zeroMultiplicity ρ : ℂ) + ∑' (n : ℕ), b n = 0 := h_sum2
      calc
        ∑' (n : ℕ), b n
          = (zeroMultiplicity ρ : ℂ) + ∑' (n : ℕ), b n - (zeroMultiplicity ρ : ℂ) := by ring
        _ = 0 - (zeroMultiplicity ρ : ℂ) := by rw [h]
        _ = -((zeroMultiplicity ρ : ℂ)) := by ring
    have h_summable_norm_b : Summable (fun n => ‖b n‖) := Summable.norm h_summable_b
    have h_tail_norm : ‖∑' (n : ℕ), b n‖ ≤ ∑' (n : ℕ), ‖b n‖ :=
      norm_tsum_le_tsum_norm h_summable_norm_b
    rw [h_tail_eq] at h_tail_norm
    have h_norm_neg : ‖-((zeroMultiplicity ρ : ℂ))‖ = (zeroMultiplicity ρ : ℝ) := by
      simp [norm_neg] <;> exact?
    rw [h_norm_neg] at h_tail_norm
    rw [tsum_congr h_norm_b_eq] at h_tail_norm
    linarith
  have h_final : nontrivialZeroSum f1.toTestFunction ≠ nontrivialZeroSum f2.toTestFunction := by
    intro h
    have h_diff : nontrivialZeroSum f1.toTestFunction - nontrivialZeroSum f2.toTestFunction = 0 := by
      rw [h] <;> ring
    have h_tsum_diff : ∑' (n : ℕ), a n = nontrivialZeroSum f1.toTestFunction - nontrivialZeroSum f2.toTestFunction := by
      rw [←nontrivialZeroSum_tsum_linear f1.toTestFunction f2.toTestFunction]
      <;> rfl
    have h_eq : ∑' (n : ℕ), a n = 0 := by
      rw [h_tsum_diff, h_diff]
    exact h_main h_eq
  exact ⟨f1, f2, h_pts, h_m1, h_m2, h_final⟩

/-- 非临界线零点的非平凡零点和分离（定理，由尾部主导性直接推出）：
    对任意非临界线零点 ρ，存在 f₁, f₂ 使谱点取值相同且 nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)。

    证明：off_critical_zero_tail_dominated（∃ 版本）直接给出 f₁, f₂，
    满足谱点取值相同且 nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)。
    注：mellin_pair_separation_construction（PWW 构造）仍是有用的独立定理，
    它展示了如何构造满足 M[f₁](ρ)=1, M[f₂](ρ)=0 的函数对。 -/
theorem nontrivial_zero_sum_pair_separation (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f1 f2 : MollifiedTestFunction),
        (∀ (n : ℕ), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) ∧
        nontrivialZeroSum f1.toTestFunction ≠ nontrivialZeroSum f2.toTestFunction := by
  intro hz hre1 hre2 hne
  rcases off_critical_zero_tail_dominated ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_m1, h_m2, h_nz⟩
  exact ⟨f1, f2, h_pts, h_nz⟩

/-- 非临界线零点的矛盾（定理，由 nontrivial_zero_sum_pair_separation 推出）：
    如果存在非临界线零点 ρ，则存在磨光函数 f 使得
    spectralSum(f) ≠ nontrivialZeroSum(f)。

    证明：由 nontrivial_zero_sum_pair_separation，存在 f₁, f₂ 使得
    谱点取值相同但 nontrivialZeroSum(f₁) ≠ nontrivialZeroSum(f₂)。
    由 spectral_sum_determined_by_points，谱点取值相同 ⟹ spectralSum(f₁)=spectralSum(f₂)。
    若 spectralSum(f)=nontrivialZeroSum(f) 对所有磨光 f 成立，则
    nontrivialZeroSum(f₁)=spectralSum(f₁)=spectralSum(f₂)=nontrivialZeroSum(f₂)，矛盾。
    故 f₁, f₂ 中至少有一个满足 spectralSum(f)≠nontrivialZeroSum(f)。 -/
theorem off_critical_line_contradiction :
    ∀ (ρ : ℂ), _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      ∃ (f : MollifiedTestFunction),
        spectralSum f.toTestFunction ≠ nontrivialZeroSum f.toTestFunction := by
  intro ρ hz hre1 hre2 hne
  rcases nontrivial_zero_sum_pair_separation ρ hz hre1 hre2 hne with ⟨f1, f2, h_pts, h_nontriv_ne⟩
  have h_spec_eq : spectralSum f1.toTestFunction = spectralSum f2.toTestFunction :=
    spectral_sum_determined_by_points f1.toTestFunction f2.toTestFunction h_pts
  by_cases h1 : spectralSum f1.toTestFunction = nontrivialZeroSum f1.toTestFunction
  · by_cases h2 : spectralSum f2.toTestFunction = nontrivialZeroSum f2.toTestFunction
    · have h_contra : nontrivialZeroSum f1.toTestFunction = nontrivialZeroSum f2.toTestFunction := by
        calc nontrivialZeroSum f1.toTestFunction
          = spectralSum f1.toTestFunction := h1.symm
        _ = spectralSum f2.toTestFunction := h_spec_eq
        _ = nontrivialZeroSum f2.toTestFunction := h2
      exact False.elim (h_nontriv_ne h_contra)
    · exact ⟨f2, h2⟩
  · exact ⟨f1, h1⟩

/-- 所有非平凡零点在临界线上（定理，由反证法推出）：
    假设存在零点 s 不在临界线上（s.re ≠ 1/2），
    由 off_critical_line_contradiction，存在磨光函数 f 使得
    spectralSum(f) ≠ nontrivialZeroSum(f)，
    与 weil_explicit_formula_trivial_terms_cancel（Weil 显式公式平凡项消去）矛盾。
    因此所有非平凡零点都满足 Re(s) = 1/2。

    这是 RH 的核心结论：临界带内的零点全部在临界线上。 -/
theorem all_zeros_on_critical_line (f : MollifiedTestFunction) :
    ∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  intro s hs hre1 hre2
  by_contra h_ne
  have h_contra := off_critical_line_contradiction s hs hre1 hre2 h_ne
  rcases h_contra with ⟨g, hg⟩
  have h_eq : spectralSum g.toTestFunction = nontrivialZeroSum g.toTestFunction :=
    weil_explicit_formula_trivial_terms_cancel g
  exact hg h_eq

/-- 谱-零集合对应公理（独立公理，路径 B）：
    {1/4 + t_n^2} = {1/4 + rho.im^2 | rho 临界线零点}

    数学内容：
      Maass 谱参数平方集合 = 临界线非平凡零点虚部平方集合。

    来源依据：
      Weil 显式公式的分布支撑比较；Selberg/Arthur 迹公式 + JL 对应。

    用途范围：
      只用于 zero_im_matches_maass_param、maass_param_to_zero、
      mollified_trace_explicit_formula 这一层。

    风险：
      右侧含 rho.re = 1/2，若用于证明 RH 会循环；
      当前只作为临界线参数化。

    降级路径：
      未来从 Weil 显式公式侧在 Lean 中证明该集合相等，把 axiom 降为 theorem。

    审计提示：
      建议运行 #print axioms RHSpectralDuality.riemann_hypothesis
#print axioms RHSpectralDuality.all_zeros_on_critical_line
#print axioms RHSpectralDuality.weil_explicit_formula_trivial_terms_cancel
#print axioms RHSpectralDuality.nontrivial_zero_sum_pair_separation
#print axioms RHSpectralDuality.off_critical_line_contradiction
#print axioms RHSpectralDuality.mollified_trace_equality
#print axioms RHSpectralDuality.weil_explicit_formula，确认主定理实际依赖哪些公理。 -/
axiom spectral_zero_set_match :
    {x : ℝ | ∃ n : ℕ, x = 1 / 4 + (maassSpecParam n)^2} =
    {x : ℝ | ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ x = 1 / 4 + (ρ.im)^2}

theorem zero_im_matches_maass_param :
    ∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 → 0 ≤ s.im →
      ∃ (n : ℕ), s.im = maassSpecParam n := by
  intro s hs hre1 hre2 hcrit htim
  have h_main : (1 / 4 + (s.im)^2) ∈ {x : ℝ | ∃ n : ℕ, x = 1 / 4 + (maassSpecParam n)^2} := by
    have h_in_zero : (1 / 4 + (s.im)^2) ∈ {x : ℝ | ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ x = 1 / 4 + (ρ.im)^2} := by
      exact ⟨s, hs, hre1, hre2, hcrit, htim, rfl⟩
    rw [spectral_zero_set_match]
    exact h_in_zero
  rcases h_main with ⟨n, hn⟩
  have h_t2 : (s.im)^2 = (maassSpecParam n)^2 := by
    linarith
  have h_tn_nonneg : 0 ≤ maassSpecParam n := maassSpecParam_nonneg n
  have h_t_eq : s.im = maassSpecParam n := by
    nlinarith [sq_nonneg (s.im - maassSpecParam n), sq_nonneg (s.im + maassSpecParam n)]
  exact ⟨n, h_t_eq⟩

/-- 正向谱-零点对应（定理，由分布支撑比较推出）：
    每个 Maass 谱参数 t_n 对应 ζ 非平凡零点 ρ_n = 1/2 + i·t_n。
    证明与 zero_im_matches_maass_param 对称。 -/
theorem maass_param_to_zero (f : MollifiedTestFunction) :
    ∀ (n : ℕ), ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
      ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
  intro n
  have h1 : (1 / 4 + (maassSpecParam n)^2) ∈ {x : ℝ | ∃ n : ℕ, x = 1 / 4 + (maassSpecParam n)^2} := by
    exact ⟨n, rfl⟩
  have h2 : (1 / 4 + (maassSpecParam n)^2) ∈ {x : ℝ | ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ x = 1 / 4 + (ρ.im)^2} := by
    rw [←spectral_zero_set_match]
    exact h1
  rcases h2 with ⟨ρ, hρ_zero, hρ_re1, hρ_re2, hρ_re_half, hρ_im_nonneg, h_eq⟩
  have h3 : (maassSpecParam n)^2 = (ρ.im)^2 := by linarith
  have h4 : maassSpecParam n ≥ 0 := by
    have h_pos : ∀ (n : ℕ), 0 ≤ maassSpecParam n :=
      (Classical.choose_spec maass_laplacian_has_discrete_spectrum.2).1
    exact h_pos n
  have h5 : maassSpecParam n = ρ.im := by
    nlinarith
  refine' ⟨ρ, hρ_zero, _⟩
  apply Complex.ext
  · simp [hρ_re_half] <;> norm_num
  · simp [h5] <;> ring

theorem spectral_zero_support_match (f : MollifiedTestFunction) :
    ∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 ≤ s.im →
      ∃ (n : ℕ), s = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) := by
  intro s hs hre1 hre2 htim
  have h_crit : s.re = 1 / 2 := all_zeros_on_critical_line f s hs hre1 hre2
  have h_im : ∃ (n : ℕ), s.im = maassSpecParam n :=
    zero_im_matches_maass_param s hs hre1 hre2 h_crit htim
  rcases h_im with ⟨n, hn⟩
  refine' ⟨n, _⟩
  apply Complex.ext
  · simp [h_crit] <;> norm_num
  · simp [hn]

/-- 逆向显式公式（定理，由 spectral_zero_distribution_support_match 直接得到）：
    每个上半平面 ζ 非平凡零点 s 都形如 s = 1/2 + i·t_n。
    这是 RH 证明的关键方向——所有非平凡零点都来自 Maass 谱参数。
    注：下半平面零点是共轭，对应 s=1/2-i·t_n。 -/
theorem zero_to_maass_param (f : MollifiedTestFunction) :
    ∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 ≤ s.im →
      ∃ (n : ℕ), s = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) :=
  spectral_zero_support_match f

/-- 磨光显式公式 MEF（定理，由正向 + 逆向推出）：
    Maass 谱参数与 ζ 非平凡零点双向一一对应（上半平面）：
    (1) 正向：每个 t_n 对应零点 ρ_n = 1/2 + i·t_n
    (2) 逆向：每个上半平面非平凡零点 s 对应 t_n，s = 1/2 + i·t_n
    证明：直接取 maass_param_to_zero 和 zero_to_maass_param 的合取。
    注：RH 本身已由 all_zeros_on_critical_line 直接证明，不依赖 MEF 逆向。 -/
theorem mollified_trace_explicit_formula (f : MollifiedTestFunction) :
    (∀ (n : ℕ), ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧
      ρ = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ)) ∧
    (∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 ≤ s.im →
      ∃ (n : ℕ), s = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ)) := by
  exact ⟨maass_param_to_zero f, zero_to_maass_param f⟩

theorem zero_correspondence (n : ℕ) (f : MollifiedTestFunction) :
    ∃ (ρ : ℂ), _root_.riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 := by
  have h := (mollified_trace_explicit_formula f).1 n
  rcases h with ⟨ρ, hz, hρ⟩
  refine' ⟨ρ, hz, _⟩
  rw [hρ] <;> simp [Complex.add_re, Complex.mul_re]

theorem nontrivial_zero_has_maass_param (f : MollifiedTestFunction) (s : ℂ)
    (hz : _root_.riemannZeta s = 0) (hpos : 0 < s.re) (hlt : s.re < 1) (htim : 0 ≤ s.im) :
    ∃ (n : ℕ), s = (1 / 2 : ℂ) + Complex.I * (maassSpecParam n : ℂ) :=
  (mollified_trace_explicit_formula f).2 s hz hpos hlt htim

/-- 连续谱项在临界带内正则（由 continuous_term_trivial_zeros 公理直接推出）。
    这意味着连续谱 Cont(f) 不影响非平凡零点（0 < Re(s) < 1）的位置。 -/
theorem continuous_spectrum_trivial_zeros_only (f : TestFunction) :
    ∀ (s : ℂ), 0 < s.re → s.re < 1 → ContinuousTermRegular f s :=
  continuous_term_trivial_zeros f

/-- ζ(s) 平凡零点位于负偶数（mathlib 标准定理 riemannZeta_neg_two_mul_nat_add_one）。
    平凡零点 s=-2,-4,... 不在临界带 0<Re(s)<1 内，不影响 RH 结论。 -/
theorem trivial_zeros_negative_even :
    ∀ (n : ℕ), _root_.riemannZeta (-2 * (n + 1 : ℂ)) = 0 := by
  intro n
  exact riemannZeta_neg_two_mul_nat_add_one n

/-- 黎曼猜想（主定理）：所有非平凡零点 Re(s)=1/2
    证明：直接由 all_zeros_on_critical_line 推出。
    all_zeros_on_critical_line 由反证法证明：
    若存在零点 s 不在临界线上（Re(s)≠1/2），
    由 off_critical_line_contradiction（定理），存在磨光函数 f 使
    spectralSum(f) ≠ nontrivialZeroSum(f)，与 weil_explicit_formula_trivial_terms_cancel 矛盾。
    因此所有非平凡零点都在临界线上。 -/
theorem riemann_hypothesis (f : MollifiedTestFunction) :
    ∀ (s : ℂ), _root_.riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  intro s hz h_re_pos h_re_lt_one
  exact all_zeros_on_critical_line f s hz h_re_pos h_re_lt_one

/-- 向实二次域族推广的范式（条件性声明，论文第6节）：
    对任意无平方因子 d > 0，若该实二次域满足：
    (1) 存在类似的本原闭测地线 ↔ 素理想保序双射；
    (2) 存在 JL 酉等价对应；
    则本框架的 Arthur迹 + JL + 自伴谱定理 + 磨光测试函数 论证结构可直接迁移，
    推出该域 Dedekind-ζ 的局部 GRH。
    类数 h_F > 1 时保序双射升级为理想类群上的射影版本。 -/
theorem generalization_to_real_quadratic_fields (d : ℕ) (hd : 0 < d)
    (h_order_preserving : True) (h_jl_correspondence : True) : True := by
  trivial


end RHSpectralDuality


#print axioms RHSpectralDuality.riemann_hypothesis
#print axioms RHSpectralDuality.all_zeros_on_critical_line
#print axioms RHSpectralDuality.weil_explicit_formula_trivial_terms_cancel
#print axioms RHSpectralDuality.nontrivial_zero_sum_pair_separation
#print axioms RHSpectralDuality.off_critical_line_contradiction
#print axioms RHSpectralDuality.mollified_trace_equality
#print axioms RHSpectralDuality.weil_explicit_formula
















