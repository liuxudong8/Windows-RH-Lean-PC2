import BSD.LSeries5
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
open BigOperators
open BSD.LSeries5

/- ①c 后半 · 第一块：e^(−α·51) < 1/10⁴ -/
theorem exp_neg_alpha_51_lt : Real.exp (-alphaE5 * (51 : ℕ)) < (1 : ℝ) / 10 ^ 4 := by
  have hp1 : Real.exp (-alphaE5 * (51 : ℕ)) = (Real.exp (-alphaE5)) ^ 51 := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  have he : Real.exp (-alphaE5 * (51 : ℕ)) ≤ ((0.8136 : ℝ) ^ 51) := by
    rw [hp1]
    exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Real.exp (-alphaE5))
      (by simpa [alphaE5] using exp_neg_alpha_lt_8136.le) 51
  have hq : ((1017 : ℚ) / 1250) ^ 51 < (1 : ℚ) / 10 ^ 4 := by native_decide
  have hnum : ((0.8136 : ℝ) ^ 51) < (1 : ℝ) / 10 ^ 4 := by
    have hq' : (((1017 : ℚ) / 1250) ^ 51 : ℝ) < ((1 : ℚ) / 10 ^ 4 : ℝ) := by
      exact_mod_cast hq
    norm_num at hq' ⊢
  exact lt_of_le_of_lt he hnum

/- ①c 后半 · 第二块：尾界 4·e^(−α·51)/(1−e^(−α)) < 5 -/
theorem tail51_bound : (4 : ℝ) * Real.exp (-alphaE5 * (51 : ℕ))
    / (1 - Real.exp (-alphaE5)) < (5 : ℝ) := by
  have h1 : (0.1864 : ℝ) < 1 - Real.exp (-alphaE5) := by
    dsimp [alphaE5]
    linarith [exp_neg_alpha_lt_8136]
  have h2 : (4 : ℝ) * Real.exp (-alphaE5 * (51 : ℕ)) ≤ (4 : ℝ) * ((1 : ℝ) / 10 ^ 4) := by
    exact mul_le_mul_of_nonneg_left exp_neg_alpha_51_lt.le (by norm_num : (0 : ℝ) ≤ 4)
  have h3 : 1 / (1 - Real.exp (-alphaE5)) ≤ 1 / (0.1864 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 0.1864) h1.le
  have he1 : Real.exp (-alphaE5) < 1 := by
    dsimp [alphaE5]
    exact lt_trans exp_neg_alpha_lt_8136 (by norm_num : (0.8136 : ℝ) < 1)
  have hc0 : (0 : ℝ) ≤ 1 / (1 - Real.exp (-alphaE5)) := by
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt (sub_pos.2 he1))
  have hb0 : (0 : ℝ) ≤ (4 : ℝ) * ((1 : ℝ) / 10 ^ 4) := by positivity
  have h4 : (4 : ℝ) * Real.exp (-alphaE5 * (51 : ℕ))
      * (1 / (1 - Real.exp (-alphaE5))) ≤
      (4 : ℝ) * ((1 : ℝ) / 10 ^ 4) * (1 / (0.1864 : ℝ)) := by
    exact mul_le_mul h2 h3 hc0 hb0
  have h5 : (4 : ℝ) * ((1 : ℝ) / 10 ^ 4) * (1 / (0.1864 : ℝ)) < (5 : ℝ) := by
    norm_num
  simpa [div_eq_mul_inv] using (lt_of_le_of_lt h4 h5)

/- ①c 后半 · 第三块：|∑' fE5(n+50)| ≤ 2·e^(−α·51)/(1−e^(−α)) -/
theorem tail_abs_le :
    |∑' n : ℕ, fE5 (n + 50)| ≤ 2 * Real.exp (-alphaE5 * (51 : ℕ)) / (1 - Real.exp (-alphaE5)) := by
  -- 0) g(n) = e^(−α(n+51)) 的可和性与和值
  have hα_pos : (0 : ℝ) < alphaE5 := by
    dsimp [alphaE5]
    exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 925))
  have hα' : ‖Real.exp (-alphaE5)‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    linarith
  have hb := hasSum_geometric_of_norm_lt_one hα'
  have hg0 : HasSum (fun n : ℕ ↦ (Real.exp (-alphaE5)) ^ 51 * (Real.exp (-alphaE5)) ^ n)
      ((Real.exp (-alphaE5)) ^ 51 * (1 - Real.exp (-alphaE5))⁻¹) := by
    exact hb.mul_left ((Real.exp (-alphaE5)) ^ 51)
  have hp : ∀ n : ℕ, (Real.exp (-alphaE5)) ^ 51 * (Real.exp (-alphaE5)) ^ n =
      Real.exp (-alphaE5 * (n + 51 : ℕ)) := by
    intro n
    rw [← pow_add]
    have hswap : 51 + n = n + 51 := by omega
    rw [hswap]
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    ring
  have hg' : HasSum (fun n : ℕ ↦ Real.exp (-alphaE5 * (n + 51 : ℕ)))
      ((Real.exp (-alphaE5)) ^ 51 * (1 - Real.exp (-alphaE5))⁻¹) := by
    exact hg0.congr_fun (fun n : ℕ ↦ (hp n).symm)
  have hg : HasSum (fun n : ℕ ↦ Real.exp (-alphaE5 * (n + 51 : ℕ)))
      ((Real.exp (-alphaE5)) ^ 51 / (1 - Real.exp (-alphaE5))) := by
    simpa [div_eq_mul_inv] using hg'
  have hgs : Summable (fun n : ℕ ↦ Real.exp (-alphaE5 * (n + 51 : ℕ))) := by
    exact ⟨_, hg⟩
  have hg_sum : Summable (fun n : ℕ ↦ 2 * Real.exp (-alphaE5 * (n + 51 : ℕ))) := by
    exact hgs.mul_left 2
  have hg_value : (∑' n : ℕ, Real.exp (-alphaE5 * (n + 51 : ℕ))) =
      Real.exp (-alphaE5 * (51 : ℕ)) / (1 - Real.exp (-alphaE5)) := by
    have hval : (Real.exp (-alphaE5)) ^ 51 / (1 - Real.exp (-alphaE5)) =
        Real.exp (-alphaE5 * (51 : ℕ)) / (1 - Real.exp (-alphaE5)) := by
      have hp51 : (Real.exp (-alphaE5)) ^ 51 = Real.exp (-alphaE5 * (51 : ℕ)) := by
        rw [← Real.exp_nat_mul]
        apply congrArg Real.exp
        ring
      rw [hp51]
    simpa [hval] using hg.tsum_eq
  -- 1) 逐项绝对值界
  have hterm : ∀ n : ℕ, |fE5 (n + 50)| ≤ 2 * Real.exp (-alphaE5 * (n + 51 : ℕ)) := by
    intro n
    have hk : (n + 50 + 1 : ℕ) = n + 51 := by omega
    have hcast : (↑(n + 50) + 1 : ℝ) = ↑(n + 51) := by
      calc
        (↑(n + 50) + 1 : ℝ) = ↑((n + 50) + 1) := by
          rw [show (1 : ℝ) = ↑(1 : ℕ) by norm_num]
          rw [← Nat.cast_add]
        _ = ↑(n + 51) := by simp [hk]
    unfold fE5
    rw [abs_mul]
    rw [hk, hcast]
    have hnn : (0 : ℝ) ≤ ((n + 51 : ℕ) : ℝ) := by positivity
    have hdiv : |(aE5 (n + 51 : ℕ) : ℝ) / ((n + 51 : ℕ) : ℝ)| ≤ 2 := by
      rw [abs_div]
      rw [abs_of_nonneg hnn]
      have hc : |(aE5 (n + 51 : ℕ) : ℝ)| ≤ 2 * ((n + 51 : ℕ) : ℝ) := by
        exact_mod_cast coefficient_bound_aE5 (n + 51)
      calc
        |(aE5 (n + 51 : ℕ) : ℝ)| / ((n + 51 : ℕ) : ℝ)
            ≤ (2 * ((n + 51 : ℕ) : ℝ)) / ((n + 51 : ℕ) : ℝ) := by
              exact div_le_div_of_nonneg_right hc hnn
        _ = 2 := by
          have hx : ((n + 51 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hx]
    have he : |Real.exp (-alphaE5 * (n + 51 : ℕ))| = Real.exp (-alphaE5 * (n + 51 : ℕ)) := by
      rw [abs_of_pos (Real.exp_pos _)]
    rw [he]
    exact mul_le_mul_of_nonneg_right hdiv (Real.exp_pos _).le
  -- 2) Σ' |fE5(n+50)| ≤ Σ' g
  have hf_abs_sum : Summable (fun n : ℕ ↦ |fE5 (n + 50)|) := by
    have hinj : Function.Injective (fun n : ℕ ↦ n + 50) := by
      intro a b h
      dsimp at h
      omega
    have hs : Summable (fun n : ℕ ↦ fE5 (n + 50)) := summable_fE5.comp_injective hinj
    exact hs.norm
  have hsum_le : (∑' n : ℕ, |fE5 (n + 50)|) ≤
      ∑' n : ℕ, 2 * Real.exp (-alphaE5 * (n + 51 : ℕ)) := by
    exact hf_abs_sum.tsum_le_tsum hterm hg_sum
  -- 3) |∑' fE5(n+50)| ≤ Σ' |fE5(n+50)|（ℝ norm = abs）
  have habs : |∑' n : ℕ, fE5 (n + 50)| ≤ ∑' n : ℕ, |fE5 (n + 50)| := by
    have hnorm : ‖∑' n : ℕ, fE5 (n + 50)‖ ≤ ∑' n : ℕ, ‖fE5 (n + 50)‖ :=
      norm_tsum_le_tsum_norm hf_abs_sum
    simpa [Real.norm_eq_abs] using hnorm
  -- 4) 拼装
  calc
    |∑' n : ℕ, fE5 (n + 50)| ≤ ∑' n : ℕ, |fE5 (n + 50)| := habs
    _ ≤ ∑' n : ℕ, 2 * Real.exp (-alphaE5 * (n + 51 : ℕ)) := hsum_le
    _ = 2 * (Real.exp (-alphaE5 * (51 : ℕ)) / (1 - Real.exp (-alphaE5))) := by
      rw [tsum_mul_left, hg_value]
    _ = 2 * Real.exp (-alphaE5 * (51 : ℕ)) / (1 - Real.exp (-alphaE5)) := by ring

end
