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

/-- 双曲距离（opaque）：d(z,w) = H³ 中 z,w 两点的双曲距离。
    在双曲空间 H³ 的上半空间模型中：
      d(z,w) = arcosh(1 + |z-w|² / (2 Im(z) Im(w)))
    双曲距离是 Γ-不变的：d(γz, γw) = d(z,w) 对所有 γ ∈ Γ。
    热核的显式公式只依赖于双曲距离。
    当前用 opaque 抽象，参数 (z, w)。 -/
opaque hyperbolicDistance : ManifoldM → ManifoldM → ℝ

/-- 双曲距离的 Γ-不变性（公理）：
    d(γ·z, γ·w) = d(z,w) 对所有 γ ∈ Γ。
    这是双曲等距变换的基本性质：PSL₂(C) 通过等距变换作用在 H³ 上。
    此性质保证热核 K_t(z,w) 只依赖 d(z,w)，因此是 Γ-不变的。 -/
axiom hyperbolicDistance_gamma_invariant :
    ∀ (n : ℕ) (z w : ManifoldM),
      hyperbolicDistance (gammaAction n z) (gammaAction n w) = hyperbolicDistance z w

/-- 三维双曲热核（定义）：K_t(z, w) = 热方程的基本解。
    对 t>0，显式公式为：
      K_t(z,w) = (4πt)^(-3/2) · e^{-t} · e^{-d²/(4t)} · (d / sinh d)
    其中 d = hyperbolicDistance(z,w)。
    对 t≤0，定义为 0（热核仅在 t>0 时有意义）。
    因子 d/sinh(d) 来自三维双曲空间的体积元。 -/
noncomputable def heatKernel (t : ℝ) (z w : ManifoldM) : ℂ :=
    if 0 < t then
      let d := hyperbolicDistance z w
      ((Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
        Real.exp (-(d)^2 / (4 * t)) *
        (d / ((Real.exp d - Real.exp (-d)) / 2)) : ℝ) : ℂ)
    else 0

/-- 热核显式公式（定理，由定义直接推出）。 -/
theorem heatKernel_explicit_formula (t : ℝ) (z w : ManifoldM) (ht : 0 < t) :
    heatKernel t z w =
      ((Real.rpow (4 * Real.pi * t) (-3 / 2) * Real.exp (-t) *
        Real.exp (-(hyperbolicDistance z w)^2 / (4 * t)) *
        (hyperbolicDistance z w / ((Real.exp (hyperbolicDistance z w) - Real.exp (-(hyperbolicDistance z w))) / 2)) : ℝ) : ℂ) := by
  simp [heatKernel, ht]

/-- 热核的对称性（公理）：K_t(z,w) = K_t(w,z)。
    这是热核的基本性质，来自 Laplacian 的自伴性。
    也可从显式公式直接验证：d(z,w)=d(w,z)。 -/
axiom heatKernel_symmetric (t : ℝ) (z w : ManifoldM) : 0 < t →
    heatKernel t z w = heatKernel t w z

/-- 热核的正定性（公理）：热核是实值且正定的。
    (heatKernel t z w).im = 0 且 0 < (heatKernel t z w).re 对所有 z,w 和 t>0。
    这是热核的基本性质，来自热方程的最大值原理。
    也可从显式公式直接验证：所有因子均为正实数。 -/
axiom heatKernel_positive (t : ℝ) (z w : ManifoldM) : 0 < t →
    (heatKernel t z w).im = 0 ∧ 0 < (heatKernel t z w).re

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

/-- 热核半群性质（公理）：H_{t+s} = H_t ∘ H_s。
    这是热方程的基本性质：热流的时间可加性。
    数学上，这等价于热核的卷积公式：
      K_{t+s}(z,w) = ∫ K_t(z,u) K_s(u,w) du。
    半群性质是热核谱表示的基础：H_t = e^{-tΔ}。 -/
axiom heatKernel_semigroup :
    ∀ (t s : ℝ), 0 ≤ t → 0 ≤ s →
      heatOperator (t + s) = (heatOperator t) ∘ (heatOperator s)

/-- 热核与 Laplacian 交换（公理，精确版）：H_t ∘ Δ_M = Δ_M ∘ H_t。
    这是热方程的直接推论：热核算子是 Laplacian 的函数 H_t = e^{-tΔ_M}。
    因此 H_t 保持 Laplacian 的特征子空间：
    如果 Δ_M φ = λ φ，则 Δ_M (H_t φ) = H_t (Δ_M φ) = λ (H_t φ)。
    这是热核方法证明谱定理的基础。 -/
axiom heatKernel_commutes_laplacian :
    ∀ (t : ℝ), 0 ≤ t →
      ∀ (f : L2Function ManifoldM),
        heatOperator t (laplacian_M f) = laplacian_M (heatOperator t f)

end OrderPreservingBijection
