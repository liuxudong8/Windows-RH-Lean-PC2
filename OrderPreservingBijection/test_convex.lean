import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

noncomputable section

/-- 测试 exp 复合线性函数是凸函数 -/
theorem test_exp_linear_convex (t : ℝ) :
    ConvexOn ℝ Set.univ (fun σ : ℝ => Real.exp (σ * t)) := by
  have h_exp_convex : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  let L : ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun x => x * t
      map_add' := by intro x y; ring
      map_smul' := by intro c x; simp [mul_assoc, mul_comm, mul_left_comm] <;> ring }
  have h_main : ConvexOn ℝ Set.univ (fun σ : ℝ => Real.exp (L σ)) :=
    h_exp_convex.comp_linearMap L
  have h_eq : (fun σ : ℝ => Real.exp (L σ)) = (fun σ : ℝ => Real.exp (σ * t)) := by
    funext σ
    rfl
  rw [← h_eq]
  exact h_main
