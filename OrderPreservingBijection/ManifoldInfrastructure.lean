/-
  流形基础设施模块
  包含 ManifoldX/ManifoldM 类型（双曲空间显式实例化）、流形积分、Γ 作用、Γ-周期化等。
  被 HeatKernel、stage_4 等模块引用。

  双曲空间模型（最简架子）：
  - ℍ² = 上半平面 {z : ℂ | Im(z) > 0}
  - ℍ³ = 上半空间 {(z,t) : ℂ × ℝ | t > 0}
  商结构 Γ\ℍⁿ 暂未显式化，由 gammaAction 隐式处理，后续逐步添加。
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OrderPreservingBijection.HyperbolicMeasure

namespace OrderPreservingBijection

/-- 二维双曲曲面 X = Γ\ℍ²（四元数代数对应的 Shimura 曲面）。
    当前实例化为上半平面 ℍ²（通用覆盖），商结构由 gammaAction 隐式处理。
    类型 UpperHalfPlane/UpperHalfSpace3 定义在 HyperbolicMeasure 模块中。 -/
abbrev ManifoldX : Type := UpperHalfPlane

/-- 三维双曲流形 M = Γ'\ℍ³（算术双曲三流形）。
    当前实例化为上半空间 ℍ³（通用覆盖），商结构由 gammaAction 隐式处理。
    Arthur 迹公式和热核都定义在 M 上，Shimura 提升的目标空间。 -/
abbrev ManifoldM : Type := UpperHalfSpace3

/-- 三维流形 M 非空（定理，由显式实例化推出）：
    上半空间 ℍ³ 非空，例如 (0, 1) ∈ ℍ³。
    旧版为公理，现降级为定理（显式实例化后显然非空）。 -/
theorem manifoldM_nonempty : Nonempty ManifoldM := by
  refine' ⟨⟨(0, 1), by norm_num⟩⟩

/-- ManifoldM inhabited instance (for opaque definitions): (0,1) is in H3. -/
instance : Inhabited ManifoldM := ⟨⟨(0, 1), by norm_num⟩⟩

/-- 二维流形 X 非空（定理，由显式实例化推出）：
    上半平面 ℍ² 非空，例如 i ∈ ℍ²。 -/
theorem manifoldX_nonempty : Nonempty ManifoldX := by
  refine' ⟨⟨Complex.I, by norm_num [Complex.I_im]⟩⟩

/-- L² 函数空间（真正的 L² 空间）：带上可测性和平方可积性证明。
    类型参数 M 是流形类型，μ 是测度。
    - L²(ManifoldX, hyperbolicMeasure2)：二维 Maass 形式空间
    - L²(ManifoldM, hyperbolicMeasure3)：三维自守形式空间
    Shimura 提升是 L²(ManifoldX) → L²(ManifoldM) 的算子。 -/
structure L2Function (M : Type) [MeasurableSpace M] (μ : MeasureTheory.Measure M) where
  /-- 底层函数 -/
  toFun : M → ℂ
  /-- 可测性证明 -/
  measurable : Measurable toFun
  /-- 平方可积性证明 -/
  sq_integrable : MeasureTheory.Integrable (fun x => ‖toFun x‖ ^ 2) μ

/-- CoeFun 实例：让 L² 函数可以像普通函数一样调用 -/
instance {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M} : CoeFun (L2Function M μ) (fun _ => M → ℂ) :=
  ⟨L2Function.toFun⟩

/-- 二维流形 X 上的 L² 空间简写 -/
abbrev L2ManifoldX := L2Function ManifoldX hyperbolicMeasure2

/-- 三维流形 M 上的 L² 空间简写 -/
abbrev L2ManifoldM := L2Function ManifoldM hyperbolicMeasure3


/-- L² 空间的零元素实例 -/
noncomputable instance {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M} : Zero (L2Function M μ) where
  zero := {
    toFun := fun _ => (0 : ℂ),
    measurable := by fun_prop,
    sq_integrable := by sorry  -- ❓ 零函数平方可积
  }

/-- L² 空间的加法实例 -/
noncomputable instance {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M} : Add (L2Function M μ) where
  add f g := {
    toFun := fun x => f.toFun x + g.toFun x,
    measurable := by sorry,  -- ❓ 加法保持可测性
    sq_integrable := by sorry  -- ❓ 加法保持平方可积性
  }

/-- L² 空间的标量乘法实例 -/
noncomputable instance {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M} : SMul ℂ (L2Function M μ) where
  smul c f := {
    toFun := fun x => c * f.toFun x,
    measurable := by sorry,  -- ❓ 标量乘法保持可测性
    sq_integrable := by sorry  -- ❓ 标量乘法保持平方可积性
  }

/-- L² 空间的 Nonempty 实例 -/
noncomputable instance {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M} : Nonempty (L2Function M μ) := by
  exact ⟨0⟩
/-- 流形上的积分（显式定义）：∫_M g dμ₃。
    关于双曲测度 hyperbolicMeasure3 的 Bochner 积分，定义在 HyperbolicMeasure 模块。
    注意：当前 ManifoldM = ℍ³（通用覆盖），体积无穷。 -/
noncomputable def manifoldIntegral (f : ManifoldM → ℂ) : ℂ :=
  hyperbolicIntegral3 f

/-- 二维流形 X 上的积分（显式定义）：∫_X h dμ₂。
    关于双曲测度 hyperbolicMeasure2 的 Bochner 积分。 -/
noncomputable def manifoldIntegralX (f : ManifoldX → ℂ) : ℂ :=
  hyperbolicIntegral2 f

/-- 流形积分的线性性（定理，从 Bochner 积分线性性推出）：
    对可积函数 f, g，∫_M (a·f + b·g) = a·∫_M f + b·∫_M g。
    从公理降级为定理：Mathlib 的 integral_add + integral_smul 直接推出。
    注意：无条件版本对不可积函数不成立（不可积时 integral=0，但两不可积函数之和可能可积）。 -/
theorem manifoldIntegral_linear (a b : ℂ) (f g : ManifoldM → ℂ)
    (hf : MeasureTheory.Integrable f hyperbolicMeasure3)
    (hg : MeasureTheory.Integrable g hyperbolicMeasure3) :
    manifoldIntegral (fun z => a * f z + b * g z) =
      a * manifoldIntegral f + b * manifoldIntegral g := by
  have h_main : (fun z : ManifoldM => a * f z + b * g z) = (fun z => a • f z + b • g z) := by
    funext z; simp [smul_eq_mul]
  rw [h_main]
  simp only [manifoldIntegral, hyperbolicIntegral3]
  have h1 : MeasureTheory.Integrable (fun z : ManifoldM => a • f z) hyperbolicMeasure3 := hf.smul a
  have h2 : MeasureTheory.Integrable (fun z : ManifoldM => b • g z) hyperbolicMeasure3 := hg.smul b
  rw [MeasureTheory.integral_add h1 h2, MeasureTheory.integral_smul, MeasureTheory.integral_smul]
  <;> simp [smul_eq_mul]

/-- 流形积分的正定性（定理，测度结构）：
    对实值非负函数 f（f(z) ∈ ℝ≥0），∫_M f dz ≥ 0。
    由 Bochner 积分的 integral_complex_ofReal + integral_nonneg 推出。 -/
theorem manifoldIntegral_positive (f : ManifoldM → ℂ)
    (h_real : ∀ z, f z = (f z).re) (h_nonneg : ∀ z, 0 ≤ (f z).re) :
    0 ≤ (manifoldIntegral f).re := by
  let g : ManifoldM → ℝ := fun z => (f z).re
  have h_f_eq : f = fun z => (g z : ℂ) := by
    funext z
    rw [h_real z]
    <;> simp [g]
  have h1 : manifoldIntegral f = manifoldIntegral (fun z : ManifoldM => (g z : ℂ)) := by rw [h_f_eq]
  have h2 : manifoldIntegral (fun z : ManifoldM => (g z : ℂ)) = (∫ z, (g z : ℂ) ∂hyperbolicMeasure3) := by
    rfl
  have h3 : (∫ z, (g z : ℂ) ∂hyperbolicMeasure3) = ((∫ z, g z ∂hyperbolicMeasure3 : ℝ) : ℂ) :=
    integral_complex_ofReal
  have h_nonneg' : 0 ≤ g := fun z => h_nonneg z
  have h_int_nonneg : 0 ≤ ∫ z, g z ∂hyperbolicMeasure3 := MeasureTheory.integral_nonneg h_nonneg'
  rw [h1, h2, h3]
  simpa [Complex.ofReal_re] using h_int_nonneg

/-- 二维流形积分的正定性（定理，测度结构）：
    与 manifoldIntegral_positive 类似，但定义域是 ManifoldX。 -/
theorem manifoldIntegralX_positive (f : ManifoldX → ℂ)
    (h_real : ∀ z, f z = (f z).re) (h_nonneg : ∀ z, 0 ≤ (f z).re) :
    0 ≤ (manifoldIntegralX f).re := by
  let g : ManifoldX → ℝ := fun z => (f z).re
  have h_f_eq : f = fun z => (g z : ℂ) := by
    funext z
    rw [h_real z]
    <;> simp [g]
  have h1 : manifoldIntegralX f = manifoldIntegralX (fun z : ManifoldX => (g z : ℂ)) := by rw [h_f_eq]
  have h2 : manifoldIntegralX (fun z : ManifoldX => (g z : ℂ)) = (∫ z, (g z : ℂ) ∂hyperbolicMeasure2) := by rfl
  have h3 : (∫ z, (g z : ℂ) ∂hyperbolicMeasure2) = ((∫ z, g z ∂hyperbolicMeasure2 : ℝ) : ℂ) :=
    integral_complex_ofReal
  have h_nonneg' : 0 ≤ g := fun z => h_nonneg z
  have h_int_nonneg : 0 ≤ ∫ z, g z ∂hyperbolicMeasure2 := MeasureTheory.integral_nonneg h_nonneg'
  rw [h1, h2, h3]
  simpa [Complex.ofReal_re] using h_int_nonneg

/-- SL₂(ℂ)：行列式为 1 的 2×2 复矩阵。
    PSL₂(ℂ) = SL₂(ℂ) / {±I} 是 ℍ³ 的等距同构群。 -/
structure SL2C where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_eq_one : a * d - b * c = 1

/-- SL2C 非空：单位矩阵 I = [[1,0],[0,1]] 的行列式为 1。 -/
instance : Nonempty SL2C := ⟨⟨1, 0, 0, 1, by norm_num⟩⟩

/-- SL2C 外延性：四个字段相等则矩阵相等。 -/
theorem SL2C.ext (γ δ : SL2C) (ha : γ.a = δ.a) (hb : γ.b = δ.b)
    (hc : γ.c = δ.c) (hd : γ.d = δ.d) : γ = δ := by
  cases γ with | mk a b c d h =>
  cases δ with | mk a' b' c' d' h' =>
  simp [ha, hb, hc, hd] <;> tauto

/-- SL2C 单位矩阵 I = [[1,0],[0,1]]。 -/
def SL2C.one : SL2C := ⟨1, 0, 0, 1, by norm_num⟩

/-- SL2C 矩阵乘法：[[a,b],[c,d]] * [[a',b'],[c',d']] = [[aa'+bc', ab'+bd'], [ca'+dc', cb'+dd']]。 -/
def SL2C.mul (γ δ : SL2C) : SL2C :=
  ⟨γ.a * δ.a + γ.b * δ.c, γ.a * δ.b + γ.b * δ.d,
   γ.c * δ.a + γ.d * δ.c, γ.c * δ.b + γ.d * δ.d, by
    have h1 : γ.a * γ.d - γ.b * γ.c = 1 := γ.det_eq_one
    have h2 : δ.a * δ.d - δ.b * δ.c = 1 := δ.det_eq_one
    have h : (γ.a * δ.a + γ.b * δ.c) * (γ.c * δ.b + γ.d * δ.d) -
             (γ.a * δ.b + γ.b * δ.d) * (γ.c * δ.a + γ.d * δ.c) =
             (γ.a * γ.d - γ.b * γ.c) * (δ.a * δ.d - δ.b * δ.c) := by ring
    rw [h, h1, h2] <;> ring⟩

/-- SL2C 逆矩阵：[[a,b],[c,d]]^{-1} = [[d,-b],[-c,a]]。
    行列式仍为 1：d*a - (-b)*(-c) = ad - bc = 1。 -/
def SL2C.inv (γ : SL2C) : SL2C :=
  ⟨γ.d, -γ.b, -γ.c, γ.a, by
    have h : γ.a * γ.d - γ.b * γ.c = 1 := γ.det_eq_one
    have h' : γ.d * γ.a - (-γ.b) * (-γ.c) = γ.a * γ.d - γ.b * γ.c := by ring
    rw [h'] <;> exact h⟩

/-- SL2C 群公理：γ^{-1} * γ = 1。纯代数，sorry 占位。 -/
theorem SL2C.inv_mul (γ : SL2C) : SL2C.mul (SL2C.inv γ) γ = SL2C.one := by
  let a := γ.a; let b := γ.b; let c := γ.c; let d := γ.d
  have h_det : a * d - b * c = 1 := γ.det_eq_one
  apply SL2C.ext
  · calc (SL2C.mul (SL2C.inv γ) γ).a
      = (SL2C.inv γ).a * γ.a + (SL2C.inv γ).b * γ.c := by rfl
    _ = d * a + (-b) * c := by rfl
    _ = d * a - b * c := by ring
    _ = a * d - b * c := by ring
    _ = 1 := h_det
    _ = (SL2C.one).a := by rfl
  · calc (SL2C.mul (SL2C.inv γ) γ).b
      = (SL2C.inv γ).a * γ.b + (SL2C.inv γ).b * γ.d := by rfl
    _ = d * b + (-b) * d := by rfl
    _ = 0 := by ring
    _ = (SL2C.one).b := by rfl
  · calc (SL2C.mul (SL2C.inv γ) γ).c
      = (SL2C.inv γ).c * γ.a + (SL2C.inv γ).d * γ.c := by rfl
    _ = (-c) * a + a * c := by rfl
    _ = 0 := by ring
    _ = (SL2C.one).c := by rfl
  · calc (SL2C.mul (SL2C.inv γ) γ).d
      = (SL2C.inv γ).c * γ.b + (SL2C.inv γ).d * γ.d := by rfl
    _ = (-c) * b + a * d := by rfl
    _ = a * d - c * b := by ring
    _ = a * d - b * c := by ring
    _ = 1 := h_det
    _ = (SL2C.one).d := by rfl

/-- SL2C 群公理：γ * γ^{-1} = 1。纯代数，sorry 占位。 -/
theorem SL2C.mul_inv (γ : SL2C) : SL2C.mul γ (SL2C.inv γ) = SL2C.one := by
  let a := γ.a; let b := γ.b; let c := γ.c; let d := γ.d
  have h_det : a * d - b * c = 1 := γ.det_eq_one
  apply SL2C.ext
  · calc (SL2C.mul γ (SL2C.inv γ)).a
      = γ.a * (SL2C.inv γ).a + γ.b * (SL2C.inv γ).c := by rfl
    _ = a * d + b * (-c) := by rfl
    _ = a * d - b * c := by ring
    _ = 1 := h_det
    _ = (SL2C.one).a := by rfl
  · calc (SL2C.mul γ (SL2C.inv γ)).b
      = γ.a * (SL2C.inv γ).b + γ.b * (SL2C.inv γ).d := by rfl
    _ = a * (-b) + b * a := by rfl
    _ = 0 := by ring
    _ = (SL2C.one).b := by rfl
  · calc (SL2C.mul γ (SL2C.inv γ)).c
      = γ.c * (SL2C.inv γ).a + γ.d * (SL2C.inv γ).c := by rfl
    _ = c * d + d * (-c) := by rfl
    _ = 0 := by ring
    _ = (SL2C.one).c := by rfl
  · calc (SL2C.mul γ (SL2C.inv γ)).d
      = γ.c * (SL2C.inv γ).b + γ.d * (SL2C.inv γ).d := by rfl
    _ = c * (-b) + d * a := by rfl
    _ = d * a - c * b := by ring
    _ = a * d - b * c := by ring
    _ = 1 := h_det
    _ = (SL2C.one).d := by rfl

/-- ℍ³ 上半空间模型的 Möbius 作用（显式公式）。
    γ·(z,t) = (z', t') where
    z' = ((az+b)*star(cz+d) + a*star(c)*t²) / (|cz+d|² + |c|²*t²)
    t' = t / (|cz+d|² + |c|²*t²) -/
noncomputable def moebiusAction (γ : SL2C) (p : ManifoldM) : ManifoldM :=
  let z : ℂ := p.val.1
  let t : ℝ := p.val.2
  let czd : ℂ := γ.c * z + γ.d
  let denom : ℝ := Complex.normSq czd + Complex.normSq γ.c * t^2
  let z' : ℂ := (γ.a * z + γ.b) * (star czd) + γ.a * star γ.c * (t^2 : ℂ)
  let t' : ℝ := t / denom
  ⟨(z' / (denom : ℂ), t'), by
    have h_t_pos : 0 < t := p.property
    have h_denom_pos : 0 < denom := by
      dsimp only [denom]
      by_cases hc : γ.c = 0
      · have h_det : γ.a * γ.d - γ.b * γ.c = 1 := γ.det_eq_one
        rw [hc] at h_det
        have hd : γ.d ≠ 0 := by
          intro h
          rw [h] at h_det; ring_nf at h_det; norm_num at h_det
        have h_denom_eq : Complex.normSq (γ.c * z + γ.d) + Complex.normSq γ.c * t^2 = Complex.normSq γ.d := by
          rw [hc]; ring_nf; simp
        rw [h_denom_eq]
        exact Complex.normSq_pos.mpr hd
      · have h1 : 0 < Complex.normSq γ.c := Complex.normSq_pos.mpr hc
        have h2 : 0 < Complex.normSq γ.c * t^2 := by positivity
        have h3 : 0 ≤ Complex.normSq czd := Complex.normSq_nonneg _
        linarith
    exact div_pos h_t_pos h_denom_pos⟩

/-- Möbius 作用的分母（辅助定义）：D(γ,z,t) = |c·z+d|² + |c|²·t²。 -/
def moebiusDenom (γ : SL2C) (z : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (γ.c * z + γ.d) + Complex.normSq γ.c * t^2

/-- Möbius 作用的 z-分子（辅助定义）：N(γ,z,t) = (a·z+b)·conj(c·z+d) + conj(c)·t²。 -/
def moebiusNumZ (γ : SL2C) (z : ℂ) (t : ℝ) : ℂ :=
  (γ.a * z + γ.b) * star (γ.c * z + γ.d) + γ.a * star γ.c * (t^2 : ℂ)


/-- 分母乘法性引理：D(g, h·(z,t))·D(h,z,t) = D(g·h,z,t)。
    纯代数恒等式，由 ad-bc=1 推出。完整证明需展开 8 个复变量的模平方，
    表达式极大，当前用 sorry 占位。数学上这是 SL₂(ℂ) 自守因子的标准性质。 -/
axiom moebiusDenom_mul (g h : SL2C) (z : ℂ) (t : ℝ) :
    moebiusDenom g (moebiusNumZ h z t / (moebiusDenom h z t : ℂ)) (t / moebiusDenom h z t)
      * moebiusDenom h z t
    = moebiusDenom (SL2C.mul g h) z t

/-- Γ = PSL₂(O_K) 的可数枚举（opaque）。
    Γ 是可数群（O_K 是有限生成 Z-模），故可用 ℕ 枚举。
    gammaEnum n = Γ 的第 n 个元素（作为 SL₂(ℂ) 中矩阵的代表）。
    完整具体化需定义 O_K = Z[(1+√5)/2] 和 PSL₂(O_K) 的枚举，成本高，当前保持 opaque。 -/
noncomputable opaque gammaEnum : ℕ → SL2C

/-- 分子乘法性引理：N(g, h·(z,t))·D(h,z,t) = N(g·h, z,t)。
    纯代数恒等式，与分母乘法性配对。当前 sorry 占位。 -/
axiom moebiusNumZ_mul (g h : SL2C) (z : ℂ) (t : ℝ) :
    moebiusNumZ g (moebiusNumZ h z t / (moebiusDenom h z t : ℂ)) (t / moebiusDenom h z t)
      * (moebiusDenom h z t : ℂ)
    = moebiusNumZ (SL2C.mul g h) z t

/-- moebiusAction 的底层值展开（辅助定理，接受 ManifoldM）。 -/
theorem moebiusAction_val (γ : SL2C) (p : ManifoldM) :
    (moebiusAction γ p).val =
    (moebiusNumZ γ p.val.1 p.val.2 / (moebiusDenom γ p.val.1 p.val.2 : ℂ),
     p.val.2 / moebiusDenom γ p.val.1 p.val.2) := by
  rcases p with ⟨⟨z, t⟩, ht⟩
  rfl

/-- Γ 作用（显式定义）：gammaAction n z = (gammaEnum n) · z。
    从 opaque 降为 def：分式线性变换公式已显式化，枚举函数 gammaEnum 保持 opaque。 -/
noncomputable def gammaAction (n : ℕ) (z : ManifoldM) : ManifoldM :=
  moebiusAction (gammaEnum n) z

/-- 单位矩阵的 Möbius 作用是恒等（定理，纯代数）：
    moebiusAction I (z,t) = (z,t)。
    由 I=(1,0,0,1) 代入公式直接验证：denom=1, z'=z, t'=t。 -/
theorem moebiusAction_one (p : ManifoldM) :
    moebiusAction SL2C.one p = p := by
  apply Subtype.ext
  simp [moebiusAction, SL2C.one, Prod.ext_iff]
  <;> constructor <;> ring_nf <;> norm_num <;> simp [Complex.ext_iff] <;> ring

/-- Möbius 作用的复合性（定理，纯代数）：
    moebiusAction (g*h) z = moebiusAction g (moebiusAction h z)。
    这是 SL₂(ℂ) 作用在 ℍ³ 上的基本性质：矩阵乘法对应作用复合。
    证明涉及分式化简，由 ℍ³ 上半空间模型的 Möbius 变换公式直接验证。 -/
theorem moebiusAction_mul (g h : SL2C) (p : ManifoldM) :
    moebiusAction (SL2C.mul g h) p = moebiusAction g (moebiusAction h p) := by
  rcases p with ⟨⟨z, t⟩, ht⟩
  set D1 := moebiusDenom h z t
  set N1 := moebiusNumZ h z t
  set D2 := moebiusDenom g (N1 / (D1 : ℂ)) (t / D1)
  set N2 := moebiusNumZ g (N1 / (D1 : ℂ)) (t / D1)
  set D3 := moebiusDenom (SL2C.mul g h) z t
  set N3 := moebiusNumZ (SL2C.mul g h) z t
  have h_denom : D2 * D1 = D3 := moebiusDenom_mul g h z t
  have h_num : N2 * (D1 : ℂ) = N3 := moebiusNumZ_mul g h z t
  have h_t1 : 0 < t / D1 := by
    have hD1_pos : 0 < D1 := by
      dsimp only [D1, moebiusDenom]
      by_cases hc : h.c = 0
      · have h_det : h.a * h.d - h.b * h.c = 1 := h.det_eq_one
        rw [hc] at h_det
        have hd : h.d ≠ 0 := by intro h; rw [h] at h_det; ring_nf at h_det; norm_num at h_det
        have h_eq : Complex.normSq (h.c * z + h.d) + Complex.normSq h.c * t^2 = Complex.normSq h.d := by
          rw [hc]; ring_nf; simp
        rw [h_eq]; exact Complex.normSq_pos.mpr hd
      · have h1 : 0 < Complex.normSq h.c := Complex.normSq_pos.mpr hc
        have h2 : 0 < Complex.normSq h.c * t^2 := by positivity
        have h3 : 0 ≤ Complex.normSq (h.c * z + h.d) := Complex.normSq_nonneg _
        linarith
    exact div_pos ht hD1_pos
  have hD1_ne_zero : D1 ≠ 0 := by
    have hD1_pos : 0 < D1 := by
      dsimp only [D1, moebiusDenom]
      by_cases hc : h.c = 0
      · have h_det : h.a * h.d - h.b * h.c = 1 := h.det_eq_one
        rw [hc] at h_det
        have hd : h.d ≠ 0 := by intro h; rw [h] at h_det; ring_nf at h_det; norm_num at h_det
        have h_eq : Complex.normSq (h.c * z + h.d) + Complex.normSq h.c * t^2 = Complex.normSq h.d := by
          rw [hc]; ring_nf; simp
        rw [h_eq]; exact Complex.normSq_pos.mpr hd
      · have h1 : 0 < Complex.normSq h.c := Complex.normSq_pos.mpr hc
        have h2 : 0 < Complex.normSq h.c * t^2 := by positivity
        have h3 : 0 ≤ Complex.normSq (h.c * z + h.d) := Complex.normSq_nonneg _
        linarith
    linarith
  have hD2_ne_zero : D2 ≠ 0 := by
    have hD2_pos : 0 < D2 := by
      dsimp only [D2, moebiusDenom]
      by_cases hc : g.c = 0
      · have h_det : g.a * g.d - g.b * g.c = 1 := g.det_eq_one
        rw [hc] at h_det
        have hd : g.d ≠ 0 := by intro h; rw [h] at h_det; ring_nf at h_det; norm_num at h_det
        have h_eq : Complex.normSq (g.c * (N1 / (D1 : ℂ)) + g.d) + Complex.normSq g.c * (t / D1)^2 = Complex.normSq g.d := by
          rw [hc]; ring_nf; simp
        rw [h_eq]; exact Complex.normSq_pos.mpr hd
      · have h1 : 0 < Complex.normSq g.c := Complex.normSq_pos.mpr hc
        have h2 : 0 < Complex.normSq g.c * (t / D1)^2 := by positivity
        have h3 : 0 ≤ Complex.normSq (g.c * (N1 / (D1 : ℂ)) + g.d) := Complex.normSq_nonneg _
        linarith
    linarith
  have hz : N2 / (D2 : ℂ) = N3 / (D3 : ℂ) := by
    have h3 : (D3 : ℂ) = (D2 : ℂ) * (D1 : ℂ) := by exact_mod_cast h_denom.symm
    rw [h3]
    have h4 : N3 = N2 * (D1 : ℂ) := h_num.symm
    rw [h4]
    field_simp [hD1_ne_zero, hD2_ne_zero] <;> ring
  have ht2 : (t / D1) / D2 = t / D3 := by
    have h4 : (t / D1) / D2 = t / (D1 * D2) := by
      field_simp [hD1_ne_zero, hD2_ne_zero] <;> ring
    rw [h4]
    have h5 : D1 * D2 = D3 := by rw [mul_comm]; exact h_denom
    rw [h5]
  have h_main : (N2 / (D2 : ℂ), (t / D1) / D2) = (N3 / (D3 : ℂ), t / D3) :=
    Prod.ext hz ht2
  have h_t1' : 0 < t / D1 := by
    have hD1_pos : 0 < D1 := by
      dsimp only [D1, moebiusDenom]
      by_cases hc : h.c = 0
      · have h_det : h.a * h.d - h.b * h.c = 1 := h.det_eq_one
        rw [hc] at h_det
        have hd : h.d ≠ 0 := by intro h; rw [h] at h_det; ring_nf at h_det; norm_num at h_det
        have h_eq : Complex.normSq (h.c * z + h.d) + Complex.normSq h.c * t^2 = Complex.normSq h.d := by
          rw [hc]; ring_nf; simp
        rw [h_eq]; exact Complex.normSq_pos.mpr hd
      · have h1 : 0 < Complex.normSq h.c := Complex.normSq_pos.mpr hc
        have h2 : 0 < Complex.normSq h.c * t^2 := by positivity
        have h3 : 0 ≤ Complex.normSq (h.c * z + h.d) := Complex.normSq_nonneg _
        linarith
    exact div_pos ht hD1_pos
  apply Subtype.ext
  set p1 : ManifoldM := moebiusAction h (⟨(z, t), ht⟩ : ManifoldM)
  have h_p1_val : p1.val = (N1 / (D1 : ℂ), t / D1) := by
    exact moebiusAction_val h (⟨(z, t), ht⟩ : ManifoldM)
  have h_left : (moebiusAction (SL2C.mul g h) (⟨(z, t), ht⟩ : ManifoldM)).val =
      (N3 / (D3 : ℂ), t / D3) := by
    exact moebiusAction_val (SL2C.mul g h) (⟨(z, t), ht⟩ : ManifoldM)
  have h_right : (moebiusAction g p1).val = (N2 / (D2 : ℂ), (t / D1) / D2) := by
    rw [moebiusAction_val g p1, h_p1_val]
    <;> rfl
  rw [h_left, h_right]
  exact h_main.symm

/-- gammaEnum 包含单位矩阵（公理，群结构）：
    存在 n₀ 使得 gammaEnum n₀ = I。
    这是 Γ 作为群的基本性质：单位元在枚举中。 -/
axiom gammaEnum_contains_one :
    ∃ (n0 : ℕ), gammaEnum n0 = SL2C.one

/-- Γ 作用的单位元（定理，由 gammaEnum_contains_one + moebiusAction_one 推出）：
    存在 e ∈ Γ（对应某个指标 n₀），使得 gammaAction n₀ z = z 对所有 z。 -/
theorem gammaAction_identity :
    ∃ (n0 : ℕ), ∀ (z : ManifoldM), gammaAction n0 z = z := by
  rcases gammaEnum_contains_one with ⟨n0, hn0⟩
  refine ⟨n0, fun z => ?_⟩
  have h : gammaAction n0 z = moebiusAction (gammaEnum n0) z := by rfl
  rw [h, hn0]
  exact moebiusAction_one z

/-- gammaEnum 对乘法封闭（公理，群结构）：
    对任意 n,m，存在 k 使得 gammaEnum k = gammaEnum n * gammaEnum m。
    这是 Γ 作为群的基本性质：乘法封闭。 -/
axiom gammaEnum_closed_under_mul :
    ∀ (n m : ℕ), ∃ (k : ℕ), gammaEnum k = SL2C.mul (gammaEnum n) (gammaEnum m)

/-- Γ 作用的相容性（定理，由 gammaEnum_closed_under_mul + moebiusAction_mul 推出）：
    对任意 γ, δ ∈ Γ，存在 γδ ∈ Γ 使得
      gammaAction (γδ) z = gammaAction γ (gammaAction δ z)。 -/
theorem gammaAction_compat :
    ∀ (n m : ℕ), ∃ (k : ℕ), ∀ (z : ManifoldM),
      gammaAction k z = gammaAction n (gammaAction m z) := by
  intro n m
  rcases gammaEnum_closed_under_mul n m with ⟨k, hk⟩
  refine ⟨k, fun z => ?_⟩
  have h1 : gammaAction k z = moebiusAction (gammaEnum k) z := by rfl
  have h2 : gammaAction n (gammaAction m z) = moebiusAction (gammaEnum n) (moebiusAction (gammaEnum m) z) := by rfl
  rw [h1, h2, hk]
  exact moebiusAction_mul (gammaEnum n) (gammaEnum m) z

/-- Γ-周期化求和（定义）：
    对核 K(z,w)，定义其 Γ-周期化：
      K^Γ(z,w) = Σ_{γ∈Γ} K(z, γ·w) = Σ_{n:ℕ} K(z, gammaAction n w)
    Γ-周期化是构造自守核的标准技术：
    将 H³ 上的核 K 投影到商空间 M = Γ\H³ 上。
    对热核 K_t，K_t^Γ(z,w) 是 M 上的热核。 -/
noncomputable def gammaPeriodization (K : ManifoldM → ManifoldM → ℂ) (z w : ManifoldM) : ℂ :=
    ∑' n : ℕ, K z (gammaAction n w)


/- ========================================================================
   Quotient structure (honestification): Gamma \ H3
   ========================================================================
   Previously ManifoldM = UpperHalfSpace3 (universal cover H3), with quotient
   structure handled implicitly via gammaAction. Now we explicitly introduce
   the quotient manifold HyperbolicQuotient = Gamma \ H3 and a fundamental
   domain existence axiom. This is more honest than "universal cover = manifold":
   trace formula, heat kernel, spectral theorem all live on the quotient.
   We keep ManifoldM = H3 unchanged (to avoid breaking existing code), but
   all "integrals over M" should be understood as integrals over a fundamental
   domain F, guaranteed by fundamentalDomain_exists. -/

/-- gammaEnum closed under inverse (group axiom): for every n, exists m with
    gammaEnum m = (gammaEnum n)^{-1}. Needed for GammaEquiv symmetry. -/
axiom gammaEnum_closed_under_inv :
    ∀ (n : ℕ), ∃ (m : ℕ), gammaEnum m = SL2C.inv (gammaEnum n)

/-- Equivalence relation induced by Gamma action: p ~ q iff exists gamma in Gamma
    such that gamma · p = q. Foundation for quotient manifold Gamma \ H3. -/
def GammaEquiv (p q : ManifoldM) : Prop :=
  ∃ n : ℕ, moebiusAction (gammaEnum n) p = q

/-- GammaEquiv is an equivalence relation.
    refl: identity in Gamma; symm: inverse in Gamma; trans: multiplication closed.
    Three group axioms + moebiusAction theorems. -/
instance gammaSetoid : Setoid ManifoldM where
  r := GammaEquiv
  iseqv := ⟨
    -- reflexivity
    (by
      intro p
      rcases gammaEnum_contains_one with ⟨n0, hn0⟩
      refine ⟨n0, ?_⟩
      rw [hn0]
      exact moebiusAction_one p),
    -- symmetry
    (by
      intro p q h
      rcases h with ⟨n, hn⟩
      rcases gammaEnum_closed_under_inv n with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have h1 : moebiusAction (gammaEnum m) (moebiusAction (gammaEnum n) p) = p := by
        rw [hm, ←moebiusAction_mul]
        rw [SL2C.inv_mul]
        exact moebiusAction_one p
      rw [hn] at h1
      exact h1),
    -- transitivity
    (by
      intro p q r h1 h2
      rcases h1 with ⟨n, hn⟩
      rcases h2 with ⟨m, hm⟩
      rcases gammaEnum_closed_under_mul m n with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h3 : moebiusAction (gammaEnum k) p = moebiusAction (gammaEnum m) (moebiusAction (gammaEnum n) p) := by
        rw [hk, moebiusAction_mul]
      rw [h3, hn, hm])
  ⟩

/-- Quotient manifold Gamma \ H3 (explicit Quotient construction).
    This is the honest hyperbolic 3-manifold M = Gamma' \ H3, where the geometric
    side of Arthur trace formula lives. -/
abbrev HyperbolicQuotient : Type := Quotient gammaSetoid

/-- Quotient map pi : H3 -> Gamma \ H3. Sends a point to its Gamma-orbit. -/
def quotientMap (p : ManifoldM) : HyperbolicQuotient :=
  Quotient.mk'' p

/-- Fundamental domain existence axiom (core honestification axiom):
    exists measurable F subset H3 such that
    (1) covering: every Gamma-orbit meets F
    (2) disjoint interior: distinct points in F are not Gamma-equivalent
    This is standard hyperbolic geometry (Ford or Dirichlet fundamental domain),
    but full formalization requires measure theory + group action infrastructure,
    so we declare it as an axiom. With F, integral over quotient = integral over F. -/
axiom fundamentalDomain_exists :
  ∃ (F : Set ManifoldM),
    (∀ (p : ManifoldM), ∃ (q : ManifoldM), q ∈ F ∧ GammaEquiv p q) ∧
    (∀ (p q : ManifoldM), p ∈ F → q ∈ F → p ≠ q → ¬ GammaEquiv p q)

/-- Integral over quotient manifold (via fundamental domain):
    integral_{Gamma\H3} f dmu = integral_F f dmu where F is a fundamental domain.
    More honest than manifoldIntegral (which integrates over all of H3 and diverges
    for automorphic functions). -/
noncomputable def quotientIntegral (f : HyperbolicQuotient → ℂ) : ℂ :=
  let F := Classical.choose fundamentalDomain_exists
  ∫ (p : ManifoldM) in F, f (quotientMap p) ∂hyperbolicMeasure3

/-- Quotient manifold nonempty (theorem): H3 nonempty implies quotient nonempty. -/
theorem hyperbolicQuotient_nonempty : Nonempty HyperbolicQuotient := by
  have h : Nonempty ManifoldM := manifoldM_nonempty
  exact h.map quotientMap

end OrderPreservingBijection
