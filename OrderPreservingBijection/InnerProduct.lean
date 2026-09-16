/-
  L² 内积具体化模块
  将 innerProduct 从 opaque 具体化为流形上的积分：⟨f,g⟩ = ∫ f · conj(g) dμ。
  依赖 ManifoldInfrastructure（manifoldIntegral、manifoldIntegralX）。
-/

import OrderPreservingBijection.ManifoldInfrastructure

namespace OrderPreservingBijection

/-- L²(M) 内积（具体定义）：⟨f, g⟩_M = ∫_M f(z) · conj(g(z)) dμ₃。
    关于三维双曲测度的 Bochner 积分。 -/
noncomputable def innerProductM (f g : L2Function ManifoldM) : ℂ :=
    manifoldIntegral (fun z => f z * star (g z))

/-- L²(X) 内积（具体定义）：⟨f, g⟩_X = ∫_X f(z) · conj(g(z)) dμ₂。
    关于二维双曲测度的 Bochner 积分。 -/
noncomputable def innerProductX (f g : L2Function ManifoldX) : ℂ :=
    manifoldIntegralX (fun z => f z * star (g z))

/-- 内积共轭对称性（定理，由积分共轭性质推出）：
    ⟨f, g⟩ = conj(⟨g, f⟩)。
    证明：∫ f·conj(g) = conj(∫ g·conj(f))，由积分的共轭线性性推出。 -/
theorem innerProductM_conj_sym (f g : L2Function ManifoldM) :
    innerProductM f g = star (innerProductM g f) := by
  let h : ManifoldM → ℂ := fun z => g z * star (f z)
  have h_main : star (manifoldIntegral h) = manifoldIntegral (fun z => star (h z)) := by
    simp [manifoldIntegral, hyperbolicIntegral3, integral_conj]
  have h_eq : innerProductM f g = manifoldIntegral (fun z => star (h z)) := by
    simp only [innerProductM]
    congr with z
    have h1 : star (g z * star (f z)) = f z * star (g z) := by
      rw [star_mul, star_star] <;> ring
    exact Eq.symm h1
  rw [h_eq, ← h_main]
  <;> rfl

/-- 内积正定性第一部分（定理，由积分正定性推出）：
    0 ≤ ⟨f, f⟩.re。
    证明：⟨f, f⟩ = ∫ |f|² ≥ 0，被积函数非负实值。 -/
theorem innerProductM_pos_def_re (f : L2Function ManifoldM) :
    0 ≤ (innerProductM f f).re := by
  simp only [innerProductM]
  have h1 : ∀ z, f z * star (f z) = (Complex.normSq (f z) : ℂ) := by
    intro z
    simp [Complex.normSq, Complex.ext_iff] <;> ring
  have h_real : ∀ z, (f z * star (f z)) = ((f z * star (f z))).re := by
    intro z
    rw [h1 z]
    simp [Complex.ofReal_re]
    <;> rfl
  have h_nonneg : ∀ z, 0 ≤ ((f z * star (f z))).re := by
    intro z
    have h2 : (f z * star (f z)).re = Complex.normSq (f z) := by
      rw [h1 z] <;> simp
    rw [h2]
    exact Complex.normSq_nonneg (f z)
  exact manifoldIntegral_positive (fun z => f z * star (f z)) h_real h_nonneg

/-- 内积正定性第二部分（定理，a.e. 版本，需可积性条件）：
    ⟨f, f⟩ = 0 → f = 0 a.e.
    证明：⟨f, f⟩ = ∫ |f|²，非负可积函数积分为 0 则 a.e. 为零（integral_eq_zero_iff_of_nonneg_ae）。
    注意：需 Integrable 条件，因为不可积函数的 Bochner 积分按约定为 0，此时定理不成立。 -/
theorem innerProductM_pos_def_ae (f : L2Function ManifoldM)
    (hfi : MeasureTheory.Integrable (fun z : ManifoldM => (f z * star (f z)).re) hyperbolicMeasure3) :
    innerProductM f f = 0 → ∀ᵐ z ∂hyperbolicMeasure3, f z = 0 := by
  intro h
  let g : ManifoldM → ℝ := fun z => (f z * star (f z)).re
  have hg_nonneg : 0 ≤ g := by
    intro z
    have h1 : g z = Complex.normSq (f z) := by
      simp [g, Complex.normSq] <;> ring
    rw [h1]
    exact Complex.normSq_nonneg (f z)
  have h_f_real : (fun z : ManifoldM => f z * star (f z)) = fun z => (g z : ℂ) := by
    funext z
    have h2 : f z * star (f z) = (Complex.normSq (f z) : ℂ) := by
      simp [Complex.normSq, Complex.ext_iff] <;> ring
    have h3 : (g z : ℂ) = (Complex.normSq (f z) : ℂ) := by
      simp [g, Complex.normSq] <;> ring
    rw [h2, h3]
  have h4 : manifoldIntegral (fun z : ManifoldM => f z * star (f z)) =
      (∫ z, g z ∂hyperbolicMeasure3 : ℂ) := by
    rw [h_f_real]
    simp [manifoldIntegral, hyperbolicIntegral3, integral_complex_ofReal]
  have h5 : innerProductM f f = manifoldIntegral (fun z => f z * star (f z)) := by rfl
  rw [h5] at h
  rw [h4] at h
  have h6 : (∫ z, g z ∂hyperbolicMeasure3 : ℂ) = 0 := h
  have h7 : ∫ z, g z ∂hyperbolicMeasure3 = 0 := by exact_mod_cast h6
  have h_ae_nonneg : 0 ≤ᵐ[hyperbolicMeasure3] g := Filter.Eventually.of_forall hg_nonneg
  have h8 : g =ᵐ[hyperbolicMeasure3] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_ae_nonneg hfi).mp h7
  filter_upwards [h8] with z hz
  have h9 : Complex.normSq (f z) = 0 := by
    have h10 : g z = Complex.normSq (f z) := by
      simp [g, Complex.normSq] <;> ring
    rw [h10] at hz
    exact hz
  have h11 : f z = 0 := by
    simpa [Complex.normSq_eq_zero] using h9
  exact h11

/-- X 上内积共轭对称性（定理）。 -/
theorem innerProductX_conj_sym (f g : L2Function ManifoldX) :
    innerProductX f g = star (innerProductX g f) := by
  let h : ManifoldX → ℂ := fun z => g z * star (f z)
  have h_main : star (manifoldIntegralX h) = manifoldIntegralX (fun z => star (h z)) := by
    simp [manifoldIntegralX, hyperbolicIntegral2, integral_conj]
  have h_eq : innerProductX f g = manifoldIntegralX (fun z => star (h z)) := by
    simp only [innerProductX]
    congr with z
    have h1 : star (g z * star (f z)) = f z * star (g z) := by
      rw [star_mul, star_star] <;> ring
    exact Eq.symm h1
  rw [h_eq, ← h_main]
  <;> rfl

/-- X 上内积正定性第一部分（定理）。 -/
theorem innerProductX_pos_def_re (f : L2Function ManifoldX) :
    0 ≤ (innerProductX f f).re := by
  simp only [innerProductX]
  have h1 : ∀ z, f z * star (f z) = (Complex.normSq (f z) : ℂ) := by
    intro z
    simp [Complex.normSq, Complex.ext_iff] <;> ring
  have h_real : ∀ z, (f z * star (f z)) = ((f z * star (f z))).re := by
    intro z
    rw [h1 z]
    simp [Complex.ofReal_re] <;> rfl
  have h_nonneg : ∀ z, 0 ≤ ((f z * star (f z))).re := by
    intro z
    have h2 : (f z * star (f z)).re = Complex.normSq (f z) := by
      rw [h1 z] <;> simp
    rw [h2]
    exact Complex.normSq_nonneg (f z)
  exact manifoldIntegralX_positive (fun z => f z * star (f z)) h_real h_nonneg

/-- X 上内积正定性第二部分（定理，a.e. 版本，需可积性条件）。 -/
theorem innerProductX_pos_def_ae (f : L2Function ManifoldX)
    (hfi : MeasureTheory.Integrable (fun z : ManifoldX => (f z * star (f z)).re) hyperbolicMeasure2) :
    innerProductX f f = 0 → ∀ᵐ z ∂hyperbolicMeasure2, f z = 0 := by
  intro h
  let g : ManifoldX → ℝ := fun z => (f z * star (f z)).re
  have hg_nonneg : 0 ≤ g := by
    intro z
    have h1 : g z = Complex.normSq (f z) := by
      simp [g, Complex.normSq] <;> ring
    rw [h1]
    exact Complex.normSq_nonneg (f z)
  have h_f_real : (fun z : ManifoldX => f z * star (f z)) = fun z => (g z : ℂ) := by
    funext z
    have h2 : f z * star (f z) = (Complex.normSq (f z) : ℂ) := by
      simp [Complex.normSq, Complex.ext_iff] <;> ring
    have h3 : (g z : ℂ) = (Complex.normSq (f z) : ℂ) := by
      simp [g, Complex.normSq] <;> ring
    rw [h2, h3]
  have h4 : manifoldIntegralX (fun z : ManifoldX => f z * star (f z)) =
      (∫ z, g z ∂hyperbolicMeasure2 : ℂ) := by
    rw [h_f_real]
    simp [manifoldIntegralX, hyperbolicIntegral2, integral_complex_ofReal]
  have h5 : innerProductX f f = manifoldIntegralX (fun z => f z * star (f z)) := by rfl
  rw [h5] at h
  rw [h4] at h
  have h6 : (∫ z, g z ∂hyperbolicMeasure2 : ℂ) = 0 := h
  have h7 : ∫ z, g z ∂hyperbolicMeasure2 = 0 := by exact_mod_cast h6
  have h_ae_nonneg : 0 ≤ᵐ[hyperbolicMeasure2] g := Filter.Eventually.of_forall hg_nonneg
  have h8 : g =ᵐ[hyperbolicMeasure2] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_ae_nonneg hfi).mp h7
  filter_upwards [h8] with z hz
  have h9 : Complex.normSq (f z) = 0 := by
    have h10 : g z = Complex.normSq (f z) := by
      simp [g, Complex.normSq] <;> ring
    rw [h10] at hz
    exact hz
  have h11 : f z = 0 := by
    simpa [Complex.normSq_eq_zero] using h9
  exact h11

end OrderPreservingBijection
