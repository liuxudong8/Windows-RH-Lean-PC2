/-
  HeatKernelSemigroup.lean
  Heat kernel semigroup module: downgrade heatKernel_semigroup from axiom to theorem.

  Core idea:
    Operator semigroup H_{t+s} = H_t ∘ H_s  is equivalent to  heat kernel convolution formula
      K_{t+s}(z,w) = integral_M K_t(z,u) K_s(u,w) du

  The convolution formula is a more basic, explicit analytic assertion, declared as axiom
  and target for future attack (spherical coordinates + hyperbolic law of cosines + special
  function integrals).

  Semigroup theorem proof: convolution formula + Fubini + integral_smul.
-/

import OrderPreservingBijection.HeatKernel
import OrderPreservingBijection.HeatKernelConvolution

namespace OrderPreservingBijection

/-- Heat kernel convolution formula (theorem, downgraded from axiom):
    K_{t+s}(z,w) = integral_M K_t(z,u) K_s(u,w) du  for t,s > 0.
    Proof in HeatKernelConvolution.lean: spherical coordinates (L1) + hyperbolic law
    of cosines (L2) + angular integral (L3) + radial integral (L4) + algebra. -/
theorem heatKernel_convolution_formula (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (z w : ManifoldM) :
    heatKernel (t + s) z w = heatKernelConvolution t s z w :=
  heatKernel_convolution_formula_theorem t s ht hs z w

/-- Heat kernel semigroup property (theorem, from convolution formula + Fubini + integral_smul):
    (H_{t+s} f)(z) = (H_t (H_s f))(z).
    Previously an axiom, now downgraded to theorem. -/
theorem heatKernel_semigroup (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (f : L2ManifoldM) (z : ManifoldM) :
    heatOperator (t + s) f z = heatOperator t (heatOperator s f) z := by
  -- Key identity: pull scalar out of integral via integral_smul (no integrability premise needed)
  have h_smul1 : ∀ (c : ℂ) (g : ManifoldM → ℂ),
      manifoldIntegral (fun x => c * g x) = c * manifoldIntegral g := by
    intro c g
    have h_eq : (fun x : ManifoldM => c * g x) = fun x : ManifoldM => c • g x := by
      funext x; simp [smul_eq_mul]
    rw [h_eq]
    have h : manifoldIntegral (fun x : ManifoldM => c • g x) = c • manifoldIntegral g := by
      simp only [manifoldIntegral, hyperbolicIntegral3]
      exact MeasureTheory.integral_smul c g
    rw [h]
    simp [smul_eq_mul]
  -- Step 1: for each u, K_t(z,u) * integral_w K_s(u,w)f(w) = integral_w K_t(z,u) K_s(u,w) f(w)
  have h_pull : ∀ (u : ManifoldM), heatKernel t z u * manifoldIntegral (fun w : ManifoldM => heatKernel s u w * f w) =
      manifoldIntegral (fun w : ManifoldM => heatKernel t z u * heatKernel s u w * f w) := by
    intro u
    have h_assoc : (fun w : ManifoldM => heatKernel t z u * heatKernel s u w * f w) =
        fun w : ManifoldM => heatKernel t z u * (heatKernel s u w * f w) := by
      funext w; ring
    rw [h_assoc]
    exact (h_smul1 (heatKernel t z u) (fun w => heatKernel s u w * f w)).symm
  -- Step 2: Fubini
  have h_fub : manifoldIntegral (fun u : ManifoldM => manifoldIntegral (fun w : ManifoldM => heatKernel t z u * heatKernel s u w * f w)) =
      manifoldIntegral (fun w : ManifoldM => manifoldIntegral (fun u : ManifoldM => heatKernel t z u * heatKernel s u w * f w)) := by
    exact manifoldIntegral_fubini (fun u w => heatKernel t z u * heatKernel s u w * f w)
  -- Step 3: convolution formula + pull f(w) out
  have h_conv : ∀ (w : ManifoldM), manifoldIntegral (fun u : ManifoldM => heatKernel t z u * heatKernel s u w) = heatKernel (t + s) z w := by
    intro w
    exact (heatKernel_convolution_formula t s ht hs z w).symm
  have h_pull2 : ∀ (w : ManifoldM), manifoldIntegral (fun u : ManifoldM => heatKernel t z u * heatKernel s u w * f w) =
      heatKernel (t + s) z w * f w := by
    intro w
    have h_assoc2 : (fun u : ManifoldM => heatKernel t z u * heatKernel s u w * f w) =
        fun u : ManifoldM => f w * (heatKernel t z u * heatKernel s u w) := by
      funext u; ring
    rw [h_assoc2]
    rw [h_smul1 (f w) (fun u => heatKernel t z u * heatKernel s u w), h_conv w] <;> ring
  -- Step 4: combine
  have h_main : manifoldIntegral (fun u : ManifoldM => heatKernel t z u * heatOperator s f u) =
      manifoldIntegral (fun w : ManifoldM => heatKernel (t + s) z w * f w) := by
    have h_expand : (fun u : ManifoldM => heatKernel t z u * heatOperator s f u) =
        fun u : ManifoldM => heatKernel t z u * manifoldIntegral (fun w : ManifoldM => heatKernel s u w * f w) := by
      funext u; rfl
    rw [h_expand]
    have h_step1 : manifoldIntegral (fun u : ManifoldM => heatKernel t z u * manifoldIntegral (fun w : ManifoldM => heatKernel s u w * f w)) =
        manifoldIntegral (fun u : ManifoldM => manifoldIntegral (fun w : ManifoldM => heatKernel t z u * heatKernel s u w * f w)) := by
      congr with u; exact h_pull u
    rw [h_step1, h_fub]
    congr with w; exact h_pull2 w
  simpa [heatOperator] using h_main.symm

end OrderPreservingBijection

