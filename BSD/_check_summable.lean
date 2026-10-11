import BSD.LPrime

open BSD.LPrime
open MeasureTheory

set_option maxHeartbeats 4000000

-- ①c 复刻探针：lprime1_summable 的证明体（几何级数闭合）
example : Summable (fun n : ℕ => (aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))) := by
  -- 几何级数：Σ (2/1.03)·e^{−1.03(n+1)}
  let q : ℝ := Real.exp (-(1.03 : ℝ))
  have hq_abs : |q| < 1 := by
    dsimp [q]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hb : HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hq_abs
  have hq1 : HasSum (fun n : ℕ => q ^ (n + 1)) (q * (1 - q)⁻¹) := by
    have hfun : (fun n : ℕ => q ^ (n + 1)) = fun n : ℕ => q ^ n * q := by
      funext n
      rw [← pow_succ]
    have hb' : HasSum (fun n : ℕ => q ^ n * q) ((1 - q)⁻¹ * q) := hb.mul_right q
    simpa [hfun, mul_comm, mul_left_comm, mul_assoc] using hb'
  have hpow : ∀ n : ℕ, Real.exp (-(1.03 : ℝ) * (n : ℕ)) = q ^ n := by
    intro n
    rw [mul_comm]
    rw [Real.exp_nat_mul]
  have hg : Summable (fun n : ℕ => (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ))) := by
    have hfun : (fun n : ℕ => (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)))
        = fun n : ℕ => (2 / (1.03 : ℝ)) * q ^ (n + 1) := by
      funext n
      rw [hpow (n + 1)]
    have hg' : Summable (fun n : ℕ => (2 / (1.03 : ℝ)) * q ^ (n + 1)) :=
      hq1.summable.mul_left (2 / (1.03 : ℝ))
    convert hg' using 1
  -- 逐项界
  refine Summable.of_norm_bounded hg ?_
  intro n
  rw [Real.norm_eq_abs]
  have hbnpos : 0 < bn (n + 1) := by
    dsimp [bn]
    positivity
  have hA : |aE (n + 1)| ≤ 2 * ((n + 1 : ℕ) : ℤ) := by
    by_cases hm : n + 1 ≤ 100
    · exact aE_bound (n + 1) hm
    · dsimp [aE]
      rw [if_neg hm]
      norm_num
      positivity
  have hA' : |(aE (n + 1) : ℝ) / (n + 1)| ≤ 2 := by
    have hz : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    calc
      |(aE (n + 1) : ℝ) / (n + 1)| = (|aE (n + 1)| : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        rw [abs_div]
        simp
        congr 1
        exact abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      _ ≤ 2 := by
        exact (div_le_iff₀ hz).2 (by exact_mod_cast hA)
  have hE1 : E1 (bn (n + 1)) ≤ Real.exp (-bn (n + 1)) / bn (n + 1) := E1_le (bn (n + 1)) hbnpos
  have hE1nonneg : 0 ≤ E1 (bn (n + 1)) := by
    dsimp [E1]
    exact MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_nonneg (le_of_lt (Real.exp_pos (-t))) (le_of_lt (lt_trans hbnpos ht)))
  have hstep1 : |(aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))| ≤ 2 * E1 (bn (n + 1)) := by
    calc
      |(aE (n + 1) : ℝ) / (n + 1) * E1 (bn (n + 1))|
          = |(aE (n + 1) : ℝ) / (n + 1)| * |E1 (bn (n + 1))| := by
        rw [abs_mul]
      _ = |(aE (n + 1) : ℝ) / (n + 1)| * E1 (bn (n + 1)) := by
        congr 1
        exact abs_of_nonneg hE1nonneg
      _ ≤ 2 * E1 (bn (n + 1)) := by
        exact mul_le_mul_of_nonneg_right hA' hE1nonneg
  have hstep2 : 2 * E1 (bn (n + 1)) ≤ 2 * (Real.exp (-bn (n + 1)) / bn (n + 1)) := by
    exact mul_le_mul_of_nonneg_left hE1 (by norm_num : (0 : ℝ) ≤ 2)
  have hbn103 : (n + 1 : ℝ) * 1.03 ≤ bn (n + 1) := by
    have hb1 : (1.03 : ℝ) ≤ 2 * Real.pi / Real.sqrt 37 := b1_gt_103.le
    calc
      (n + 1 : ℝ) * 1.03 ≤ (n + 1 : ℝ) * (2 * Real.pi / Real.sqrt 37) := by
        exact mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = bn (n + 1) := by
        dsimp [bn]
        norm_cast
        ring
  have hb1le : (1.03 : ℝ) ≤ bn (n + 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (by omega : (1 : ℕ) ≤ n + 1)
    calc
      (1.03 : ℝ) = (1 : ℝ) * 1.03 := by ring
      _ ≤ ((n : ℝ) + 1) * 1.03 := by
        exact mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 1.03)
      _ ≤ bn (n + 1) := by
        simpa [Nat.cast_add] using hbn103
  have hdiv : (bn (n + 1))⁻¹ ≤ (1.03 : ℝ)⁻¹ := by
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1.03) hb1le)
  have hbn103' : (1.03 : ℝ) * (n + 1 : ℕ) ≤ bn (n + 1) := by
    simpa [mul_comm] using hbn103
  have hneg : -bn (n + 1) ≤ -(1.03 : ℝ) * (n + 1 : ℕ) := by
    rw [neg_mul]
    exact neg_le_neg hbn103'
  have hmono : Real.exp (-bn (n + 1)) ≤ Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) := by
    exact (Real.exp_le_exp).mpr hneg
  have hq : Real.exp (-bn (n + 1)) / bn (n + 1) ≤
      Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) / (1.03 : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul hmono hdiv (by positivity : (0 : ℝ) ≤ (bn (n + 1))⁻¹)
      (by positivity : (0 : ℝ) ≤ Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)))
  have hstep3 : 2 * (Real.exp (-bn (n + 1)) / bn (n + 1)) ≤
      (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) := by
    calc
      2 * (Real.exp (-bn (n + 1)) / bn (n + 1)) ≤
          2 * (Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) / (1.03 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2)
      _ = (2 / (1.03 : ℝ)) * Real.exp (-(1.03 : ℝ) * (n + 1 : ℕ)) := by
        ring
  exact le_trans hstep1 (le_trans hstep2 hstep3)
