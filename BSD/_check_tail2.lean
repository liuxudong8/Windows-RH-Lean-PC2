import BSD.LPrime
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
open BigOperators
open BSD.LPrime

-- 1) aE_bound_all：m > 100 时 aE m = 0
theorem aE_bound_all (m : ℕ) : |aE m| ≤ 2 * (m : ℤ) := by
  by_cases hm : m ≤ 100
  · exact aE_bound m hm
  · dsimp [aE]
    rw [if_neg hm]
    norm_num

-- 2) bn m ≥ m·1.03
theorem bn_ge_103m (m : ℕ) : (m : ℝ) * 1.03 ≤ bn m := by
  have hb1 : (1.03 : ℝ) ≤ 2 * Real.pi / Real.sqrt 37 := b1_gt_103.le
  calc
    (m : ℝ) * 1.03 ≤ (m : ℝ) * (2 * Real.pi / Real.sqrt 37) := by
      exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = bn m := by
      dsimp [bn]
      ring

-- 3) exp 单调：bn 4 ≥ 4·1.03 ⟹ e^{-bn 4} ≤ e^{-4·1.03}
theorem exp_mono_test : Real.exp (-bn 4) ≤ Real.exp (-(4 * 1.03 : ℝ)) := by
  have hb : (4 : ℝ) * 1.03 ≤ bn 4 := by
    simpa using bn_ge_103m 4
  have hneg : -bn 4 ≤ -(4 * 1.03 : ℝ) := by linarith
  exact (Real.exp_le_exp).mpr hneg

-- 4) 几何级数：Σ' n, e^{−1.03·(n+4)} = e^{−4·1.03}/(1−e^{−1.03})
theorem geom_shift_test :
    (∑' n : ℕ, Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ))) =
      Real.exp (-(1.03 : ℝ) * 4) / (1 - Real.exp (-(1.03 : ℝ))) := by
  have hq_abs : ‖Real.exp (-(1.03 : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hb := hasSum_geometric_of_norm_lt_one hq_abs
  have hg0 : HasSum (fun n : ℕ => (Real.exp (-(1.03 : ℝ))) ^ 4 * (Real.exp (-(1.03 : ℝ))) ^ n)
      ((Real.exp (-(1.03 : ℝ))) ^ 4 * (1 - Real.exp (-(1.03 : ℝ)))⁻¹) := by
    exact hb.mul_left ((Real.exp (-(1.03 : ℝ))) ^ 4)
  have hp : ∀ n : ℕ, (Real.exp (-(1.03 : ℝ))) ^ 4 * (Real.exp (-(1.03 : ℝ))) ^ n =
      Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)) := by
    intro n
    rw [← pow_add]
    have hswap : 4 + n = n + 4 := by omega
    rw [hswap]
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  have hg' : HasSum (fun n : ℕ => Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)))
      ((Real.exp (-(1.03 : ℝ))) ^ 4 * (1 - Real.exp (-(1.03 : ℝ)))⁻¹) := by
    exact hg0.congr_fun (fun n : ℕ => (hp n).symm)
  have hg : HasSum (fun n : ℕ => Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ)))
      ((Real.exp (-(1.03 : ℝ))) ^ 4 / (1 - Real.exp (-(1.03 : ℝ)))) := by
    simpa [div_eq_mul_inv] using hg'
  have hval : (Real.exp (-(1.03 : ℝ))) ^ 4 = Real.exp (-(1.03 : ℝ) * 4) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  calc
    (∑' n : ℕ, Real.exp (-(1.03 : ℝ) * (n + 4 : ℕ))) =
        (Real.exp (-(1.03 : ℝ))) ^ 4 / (1 - Real.exp (-(1.03 : ℝ))) := hg.tsum_eq
    _ = Real.exp (-(1.03 : ℝ) * 4) / (1 - Real.exp (-(1.03 : ℝ))) := by
      rw [hval]

-- 5) 数值：e^{−4·1.03} = e^{−4.12} ≤ 0.358^4；0.358^4/(1−0.358)·(1/(2·1.03)) < 0.0125
theorem tail_num_test : (1 / (2 * (1.03 : ℝ))) * (0.358 : ℝ) ^ 4 / (1 - (0.358 : ℝ)) < (0.0125 : ℝ) := by
  norm_num

-- 6) e^{-1.03·(n+4)} ≤ 0.358^n 型衰减：e^{-1.03} ≤ 0.358
theorem exp_neg_103_ge0 : (0 : ℝ) ≤ Real.exp (-(1.03 : ℝ)) := (Real.exp_pos _).le

end
