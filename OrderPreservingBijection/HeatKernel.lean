/-
  热核模块
  包含 Laplace 变换、热核显式公式、f(Δ) 积分核、几何侧迹、热核算子等。
  依赖 ManifoldInfrastructure（ManifoldM、manifoldIntegral、gammaAction 等）
  和 BasicInfrastructure（TestFunction、realIntegral）。
-/

import OrderPreservingBijection.ManifoldInfrastructure
import OrderPreservingBijection.BasicInfrastructure
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Arcosh

namespace OrderPreservingBijection

/- 6.1 分析基础设施：Laplace 变换、Γ 作用、热核显式公式 -/

/-- Laplace 变换（def，用 realIntegral 实现）：
    L[f](t) = ∫₀^∞ f(x) e^{-tx} dx。 -/
noncomputable def laplaceTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
    realIntegral (fun x => f x * Real.exp (-t * x))

/-- Laplace 变换的指数函数计算（定理，Mathlib integral_exp_neg_mul_rpow）：
    L[e^{-sλ}](t) = 1/(t+s)，对 t,s > 0。
    由 Mathlib 的 integral_exp_neg_mul_rpow（取 p=1, b=t+s）直接推出：
      ∫₀^∞ e^{-(s+t)λ} dλ = (s+t)^{-1}·Γ(2) = 1/(s+t)。
    这个公式是热核函数演算的基础。 -/
theorem laplaceTransform_exp (s t : ℝ) : 0 < t → 0 < s →
    laplaceTransform (fun x => Real.exp (-s * x)) t = 1 / (t + s) := by
  intro ht hs
  have h_pos : 0 < t + s := by linarith
  simp only [laplaceTransform, realIntegral]
  have h_real : ∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(t + s) * x) = 1 / (t + s) := by
    have h := _root_.integral_exp_neg_mul_rpow (p := 1) (b := t + s) (by norm_num) h_pos
    have h_eq1 : (fun x : ℝ => Real.exp (-(t + s) * x)) = (fun x : ℝ => Real.exp (-(t + s) * x ^ (1 : ℝ))) := by
      funext x; simp [Real.rpow_one]
    have h1 : ∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(t + s) * x) = (t + s) ^ (-1 : ℝ) * Real.Gamma 2 := by
      rw [h_eq1]
      have h_simp : (t + s) ^ (-1 / 1 : ℝ) * Real.Gamma (1 / 1 + 1) = (t + s) ^ (-1 : ℝ) * Real.Gamma 2 := by
        norm_num
      rw [h_simp] at h
      exact h
    rw [h1]
    have h2 : (t + s) ^ (-1 : ℝ) * Real.Gamma 2 = 1 / (t + s) := by
      rw [Real.Gamma_two]
      have h3 : (t + s) ^ (-1 : ℝ) = 1 / (t + s) := by
        rw [Real.rpow_neg_one] <;> field_simp
      rw [h3] <;> ring
    rw [h2]
  have h_eq : (fun x : ℝ => (Real.exp (-s * x) * Real.exp (-t * x) : ℂ)) = fun x : ℝ => (Real.exp (-(t + s) * x) : ℂ) := by
    funext x
    have h : Real.exp (-s * x) * Real.exp (-t * x) = Real.exp (-(t + s) * x) := by
      rw [← Real.exp_add] <;> ring
    have h' : (Real.exp (-s * x) * Real.exp (-t * x) : ℂ) = (Real.exp (-(t + s) * x) : ℂ) := by
      rw [← Complex.ofReal_mul, h]
    exact h'
  rw [h_eq]
  exact_mod_cast h_real

/-- Laplace 变换的线性性（定理，由积分线性性推出）：
    L[af + bg](t) = a·L[f](t) + b·L[g](t)。
    证明：Laplace 变换是积分算子，展开定义后由 realIntegral_linear 直接推出。 -/
theorem laplaceTransform_linear (a b : ℂ) (f g : ℝ → ℂ) (t : ℝ) :
    laplaceTransform (fun x => a * f x + b * g x) t =
      a * laplaceTransform f t + b * laplaceTransform g t := by
  rw [laplaceTransform, laplaceTransform, laplaceTransform]
  have h_integrand : (fun x : ℝ => (a * f x + b * g x) * (Real.exp (-t * x) : ℂ)) =
                      (fun x : ℝ => a * (f x * (Real.exp (-t * x) : ℂ)) + b * (g x * (Real.exp (-t * x) : ℂ))) := by
    funext x
    <;> ring
  rw [h_integrand]
  exact realIntegral_linear (fun x : ℝ => f x * (Real.exp (-t * x) : ℂ)) (fun x : ℝ => g x * (Real.exp (-t * x) : ℂ)) a b

/-- 积分核的复合（定义）：
    (K1 ∘_K K2)(z,w) = ∫_M K1(z,u) K2(u,w) du。
    对应于积分算子的复合：T_{K1} ∘ T_{K2} = T_{K1 ∘_K K2}。
    这是定义迹循环性的前提。 -/
noncomputable def kernelComposition (K1 K2 : ManifoldM → ManifoldM → ℂ) :
    ManifoldM → ManifoldM → ℂ :=
  fun z w => manifoldIntegral (fun u => K1 z u * K2 u w)

/-- 流形积分的 Fubini 定理（公理，第一档标准结果）：
    ∫_M ∫_M f(z,u) du dz = ∫_M ∫_M f(z,u) dz du。
    对迹类核函数成立，是积分交换顺序的标准性质。 -/
axiom manifoldIntegral_fubini (f : ManifoldM → ManifoldM → ℂ) :
    manifoldIntegral (fun z => manifoldIntegral (fun u => f z u)) =
    manifoldIntegral (fun u => manifoldIntegral (fun z => f z u))

/-- 迹的循环性（定理，由 Fubini 定理推出）：Tr(T_{K1} ∘ T_{K2}) = Tr(T_{K2} ∘ T_{K1})。
    即复合核的对角线积分与顺序无关：
      ∫_M (K1 ∘_K K2)(z,z) dz = ∫_M (K2 ∘_K K1)(z,z) dz。
    证明：展开 kernelComposition，用 Fubini 交换积分顺序，再变量重命名 z↔u。 -/
theorem trace_cyclicity (K1 K2 : ManifoldM → ManifoldM → ℂ) :
    manifoldIntegral (fun z => kernelComposition K1 K2 z z) =
    manifoldIntegral (fun z => kernelComposition K2 K1 z z) := by
  simp [kernelComposition]
  rw [manifoldIntegral_fubini (fun z u => K1 z u * K2 u z)]
  congr
  funext u
  congr
  funext z
  <;> ring

/-- 三维双曲空间 ℍ³ 上半空间模型的双曲距离（显式定义）。
    对 p = (z, t), q = (w, s) ∈ ℍ³（z,w ∈ ℂ，t,s > 0）：
      cosh d(p,q) = 1 + (|z-w|² + (t-s)²) / (2ts)
    因此 d(p,q) = arcosh(1 + (|z-w|² + (t-s)²) / (2ts))。
    这是 ℍ³ 上半空间模型的标准距离公式。
    参数 ≥ 1：|z-w|² ≥ 0，(t-s)² ≥ 0，2ts > 0（t,s > 0），故分式 ≥ 0，1 + 分式 ≥ 1。
    旧版为 opaque，现降级为显式定义。 -/
noncomputable def hyperbolicDistance (p q : ManifoldM) : ℝ :=
  Real.arcosh (1 + (Complex.normSq (p.val.1 - q.val.1) + (p.val.2 - q.val.2)^2) / (2 * p.val.2 * q.val.2))

/-- 双曲距离参数在 arcosh 定义域内（引理）：1 + (...) ≥ 1。 -/
lemma hyperbolicDistance_arg_ge_one (p q : ManifoldM) :
    1 ≤ 1 + (Complex.normSq (p.val.1 - q.val.1) + (p.val.2 - q.val.2)^2) / (2 * p.val.2 * q.val.2) := by
  have h1 : 0 ≤ Complex.normSq (p.val.1 - q.val.1) := Complex.normSq_nonneg _
  have h2 : 0 ≤ (p.val.2 - q.val.2)^2 := by positivity
  have h3 : 0 < p.val.2 := p.property
  have h4 : 0 < q.val.2 := q.property
  have h5 : 0 < 2 * p.val.2 * q.val.2 := by positivity
  have h6 : 0 ≤ (Complex.normSq (p.val.1 - q.val.1) + (p.val.2 - q.val.2)^2) / (2 * p.val.2 * q.val.2) := by
    apply div_nonneg
    · positivity
    · positivity
  linarith

/-- 双曲距离对称性（定理，由显式公式直接推出）：d(p,q) = d(q,p)。
    公式中 |z-w|² = |w-z|²，(t-s)² = (s-t)²，分母 2ts = 2st，故对称。 -/
theorem hyperbolicDistance_symmetric (p q : ManifoldM) :
    hyperbolicDistance p q = hyperbolicDistance q p := by
  have h1 : Complex.normSq (p.val.1 - q.val.1) = Complex.normSq (q.val.1 - p.val.1) := by
    rw [show p.val.1 - q.val.1 = -(q.val.1 - p.val.1) by ring]
    rw [Complex.normSq_neg]
  have h2 : (p.val.2 - q.val.2)^2 = (q.val.2 - p.val.2)^2 := by
    rw [show p.val.2 - q.val.2 = -(q.val.2 - p.val.2) by ring]
    rw [neg_sq]
  have h3 : 2 * p.val.2 * q.val.2 = 2 * q.val.2 * p.val.2 := by ring
  simp [hyperbolicDistance, h1, h2, h3]

/-- 双曲距离的 Γ-不变性（公理）：
    d(γ·z, γ·w) = d(z,w) 对所有 γ ∈ Γ。
    这是双曲等距变换的基本性质：PSL₂(C) 通过等距变换作用在 H³ 上。
    此性质保证热核 K_t(z,w) 只依赖 d(z,w)，因此是 Γ-不变的。
    距离本身已显式化，但 gammaAction 仍为 opaque，故不变性保持为公理。 -/
axiom hyperbolicDistance_gamma_invariant :
    ∀ (n : ℕ) (z w : ManifoldM),
      hyperbolicDistance (gammaAction n z) (gammaAction n w) = hyperbolicDistance z w

/-- 双曲距离非负（定理，由 arcosh 值域推出）：d(p,q) ≥ 0。
    Real.arcosh(x) ≥ 0 对 x ≥ 1 成立，而距离参数 ≥ 1（hyperbolicDistance_arg_ge_one）。 -/
theorem hyperbolicDistance_nonneg (p q : ManifoldM) :
    0 ≤ hyperbolicDistance p q :=
  Real.arcosh_nonneg (hyperbolicDistance_arg_ge_one p q)

/-- d/sinh(d) 的连续延拓（定义）：
    当 d ≠ 0 时为 d/sinh(d)；当 d = 0 时取极限值 1（lim_{d→0} d/sinh(d) = 1）。
    热核公式中 d/sinh(d) 在 d=0 处有可去奇点，必须用连续延拓，否则 K_t(z,z)=0（与正定性矛盾）。
    对 d ≥ 0，d_over_sinh(d) > 0：d>0 时 d>0 且 sinh(d)>0；d=0 时值为 1。 -/
noncomputable def d_over_sinh (d : ℝ) : ℝ :=
  if d = 0 then 1 else d / Real.sinh d

/-- d_over_sinh 正性（定理）：d ≥ 0 → d_over_sinh(d) > 0。
    d=0 时值为 1；d>0 时 d>0 且 sinh(d)>0（Real.sinh_pos_iff），故商为正。 -/
theorem d_over_sinh_pos (d : ℝ) (h : 0 ≤ d) : 0 < d_over_sinh d := by
  by_cases h0 : d = 0
  · rw [d_over_sinh, h0, if_pos rfl]
    norm_num
  · have hpos : 0 < d := by
      by_contra h'
      have : d = 0 := by linarith
      exact h0 this
    rw [d_over_sinh, if_neg h0]
    apply div_pos hpos
    exact Real.sinh_pos_iff.mpr hpos

/-- d_over_sinh 连续性（公理）：d_over_sinh 在 ℝ 上连续。
    证明路径：d≠0 时显然；d=0 时用 isEquivalent_sinh (sinh ~[nhds 0] id) 得 d/sinh(d) → 1。 -/
axiom d_over_sinh_continuous : Continuous d_over_sinh

/-- 三维双曲热核（定义）：K_t(z, w) = 热方程的基本解。
    对 t>0，显式公式为：
      K_t(z,w) = (4πt)^(-3/2) · e^{-t} · e^{-d²/(4t)} · d_over_sinh(d)
    其中 d = hyperbolicDistance(z,w)，d_over_sinh 是 d/sinh(d) 的连续延拓（d=0 时为 1）。
    对 t≤0，定义为 0（热核仅在 t>0 时有意义）。
    因子 d/sinh(d) 来自三维双曲空间的体积元。 -/
noncomputable def heatKernel (t : ℝ) (z w : ManifoldM) : ℂ :=
    if 0 < t then
      let d := hyperbolicDistance z w
      ((Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
        Real.exp (-(d)^2 / (4 * t)) *
        d_over_sinh d : ℝ) : ℂ)
    else 0

/-- 热核显式公式（定理，由定义直接推出）。 -/
theorem heatKernel_explicit_formula (t : ℝ) (z w : ManifoldM) (ht : 0 < t) :
    heatKernel t z w =
      ((Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
        Real.exp (-(hyperbolicDistance z w)^2 / (4 * t)) *
        d_over_sinh (hyperbolicDistance z w) : ℝ) : ℂ) := by
  simp [heatKernel, ht]

/-- 热核的对称性（定理，由显式公式 + 距离对称性推出）：K_t(z,w) = K_t(w,z)。
    热核显式公式只依赖 d(z,w)，而 d(z,w)=d(w,z)（hyperbolicDistance_symmetric），故对称。
    旧版为公理，现降级为定理。 -/
theorem heatKernel_symmetric (t : ℝ) (z w : ManifoldM) (ht : 0 < t) :
    heatKernel t z w = heatKernel t w z := by
  rw [heatKernel_explicit_formula t z w ht, heatKernel_explicit_formula t w z ht]
  rw [hyperbolicDistance_symmetric z w]

/-- 热核的正定性（定理，由显式公式直接验证）：热核是实值且正定的。
    (heatKernel t z w).im = 0 且 0 < (heatKernel t z w).re 对所有 z,w 和 t>0。
    证明：所有因子均为正实数——
    (1) (4πt)^(-3/2) > 0（正数的实幂为正）
    (2) e^{-t} > 0（指数函数恒正）
    (3) e^{-d²/(4t)} > 0（指数函数恒正）
    (4) d_over_sinh(d) > 0（d ≥ 0，d_over_sinh_pos）
    乘积为正实数，嵌入 ℂ 后虚部为 0、实部为正。
    旧版为公理，现降级为定理。 -/
theorem heatKernel_positive (t : ℝ) (z w : ManifoldM) (ht : 0 < t) :
    (heatKernel t z w).im = 0 ∧ 0 < (heatKernel t z w).re := by
  set d := hyperbolicDistance z w with hd
  set v := Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
      Real.exp (-(d)^2 / (4 * t)) * d_over_sinh d with hv
  have h1 : 0 < Real.rpow (4 * Real.pi * t) (-3 / 2) := by
    apply Real.rpow_pos_of_pos
    positivity
  have h2 : 0 < Real.exp (-t) := Real.exp_pos _
  have h3 : 0 < Real.exp (-(d)^2 / (4 * t)) := Real.exp_pos _
  have h4 : 0 ≤ d := hyperbolicDistance_nonneg z w
  have h5 : 0 < d_over_sinh d := d_over_sinh_pos d h4
  have h6 : 0 < v := by
    rw [hv]
    positivity
  have h7 : heatKernel t z w = (v : ℂ) := by
    rw [heatKernel_explicit_formula t z w ht, hv]
    <;> rfl
  rw [h7]
  constructor
  · simp
  · have hre : ((v : ℂ)).re = v := by simp
    rw [hre]
    exact h6

/-- f(Δ) 的积分核（定义）：K_f(z, w) = ∫₀^∞ L[f](t) · K_t(z,w) dt。
    即 f(Δ) 的积分核是热核的 Laplace 变换加权积分。
    推导：由谱定理 f(Δ) = ∫ f(λ) dE(λ)，热核 e^{-tΔ} = ∫ e^{-tλ} dE(λ)，
    由 Laplace 反演得 K_f = ∫ L[f](t) K_t dt。 -/
noncomputable def fLaplacianKernel (f : TestFunction) (z w : ManifoldM) : ℂ :=
    realIntegral (fun t => laplaceTransform f t * heatKernel t z w)

/-- 几何侧迹（定义，热核积分形式）：
    Tr_geo(f) = ∫_M Σ_{γ∈Γ} K_f(z, γz) dz
    即 geometricKernelTrace f = manifoldIntegral (fun z => gammaPeriodization (fLaplacianKernel f) z z)。
    这是 Arthur 迹公式几何侧的显式积分表达式。 -/
noncomputable def geometricKernelTrace (f : TestFunction) : ℂ :=
    manifoldIntegral (fun z => gammaPeriodization (fLaplacianKernel f) z z)

/-- 三维 Laplacian（opaque，类型化）：Δ_M : L²(M) → L²(M)。 -/
opaque laplacian_M : L2Function ManifoldM → L2Function ManifoldM

/-- 热核算子（定义）：H_t = integralOperator (heatKernel t)。
    (H_t f)(z) = ∫ K_t(z,w) f(w) dw。
    热核算子是自伴的、正定的、满足半群性质 H_{t+s} = H_t H_s。
    当 t→0+ 时 H_t → Id（恒等算子），当 t→∞ 时 H_t → 投影到常数函数。 -/
noncomputable def heatOperator (t : ℝ) (f : L2Function ManifoldM) : L2Function ManifoldM :=
    fun (z : ManifoldM) => manifoldIntegral (fun (w : ManifoldM) => heatKernel t z w * f w)

/-- 热核与 Laplacian 交换（公理，精确版）：H_t ∘ Δ_M = Δ_M ∘ H_t。
    这是热方程的直接推论：热核算子是 Laplacian 的函数 H_t = e^{-tΔ_M}。
    因此 H_t 保持 Laplacian 的特征子空间：
    如果 Δ_M φ = λ φ，则 Δ_M (H_t φ) = H_t (Δ_M φ) = λ (H_t φ)。
    这是热核方法证明谱定理的基础。 -/
axiom heatKernel_commutes_laplacian :
    ∀ (t : ℝ), 0 ≤ t →
      ∀ (f : L2Function ManifoldM),
        heatOperator t (laplacian_M f) = laplacian_M (heatOperator t f)


/-- Heat kernel convolution (def): (K_t * K_s)(z,w) = integral_M K_t(z,u) K_s(u,w) du. -/
noncomputable def heatKernelConvolution (t s : ℝ) (z w : ManifoldM) : ℂ :=
    manifoldIntegral (fun u : ManifoldM => heatKernel t z u * heatKernel s u w)

end OrderPreservingBijection
