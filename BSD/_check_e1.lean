import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 4000000

noncomputable section

def E1 (b : ℝ) : ℝ := ∫ t in Set.Ioi b, Real.exp (-t) / t

open MeasureTheory

-- 逐点引理：t >= b > 0 则 e^{-t}/t <= e^{-t}/b
lemma pt_le {b t : ℝ} (hb : 0 < b) (htb : b ≤ t) :
    Real.exp (-t) / t ≤ Real.exp (-t) / b := by
  have ht_pos : 0 < t := lt_of_lt_of_le hb htb
  have h : (1 / t : ℝ) ≤ 1 / b := one_div_le_one_div_of_le hb htb
  have he : 0 ≤ Real.exp (-t) := le_of_lt (Real.exp_pos (-t))
  calc
    Real.exp (-t) / t = Real.exp (-t) * (1 / t) := by ring
    _ ≤ Real.exp (-t) * (1 / b) := mul_le_mul_of_nonneg_left h he
    _ = Real.exp (-t) / b := by ring

-- f 在 Ioi b 上连续（b > 0）
lemma cont_div (b : ℝ) (hb : 0 < b) :
    ContinuousOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi b) := by
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  · exact continuous_id.continuousOn
  · intro x hx
    exact ne_of_gt (lt_trans hb hx)

-- 主上界：∫_{Ioi b} e^{-t}/t ≤ e^{-b}/b
theorem E1_le (b : ℝ) (hb : 0 < b) :
    (∫ t in Set.Ioi b, Real.exp (-t) / t) ≤ Real.exp (-b) / b := by
  have h1 : (∫ t in Set.Ioi b, Real.exp (-t) / t) ≤
      (∫ t in Set.Ioi b, Real.exp (-t) / b) := by
    refine integral_mono_ae ?_ ?_ ?_
    · apply Integrable.mono'
      · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)
      · exact (cont_div b hb).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := lt_trans hb ht
        have htb : b ≤ t := le_of_lt ht
        have hnonneg : 0 ≤ Real.exp (-t) / t := by
          exact div_nonneg (le_of_lt (Real.exp_pos (-t))) (le_of_lt ht_pos)
        have hpt : Real.exp (-t) / t ≤ Real.exp (-t) / b := pt_le hb htb
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpt
    · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact pt_le hb (le_of_lt ht)
  calc
    (∫ t in Set.Ioi b, Real.exp (-t) / t) ≤ (∫ t in Set.Ioi b, Real.exp (-t) / b) := h1
    _ = (∫ t in Set.Ioi b, Real.exp (-t)) / b := by
      rw [← integral_div]
    _ = Real.exp (-b) / b := by
      rw [integral_exp_neg_Ioi]

-- 下界引理（分部积分的组件）：∫_{Ioi b} e^{-t}/t^2 ≤ e^{-b}/b^2
theorem E1_aux_le (b : ℝ) (hb : 0 < b) :
    (∫ t in Set.Ioi b, Real.exp (-t) / t ^ 2) ≤ Real.exp (-b) / b ^ 2 := by
  have hg : (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) = Real.exp (-b) / b ^ 2 := by
    calc
      (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) =
          b⁻¹ * (b⁻¹ * (∫ t in Set.Ioi b, Real.exp (-t))) := by
        rw [← integral_const_mul, ← integral_const_mul]
      _ = b⁻¹ * (b⁻¹ * Real.exp (-b)) := by
        rw [integral_exp_neg_Ioi]
      _ = Real.exp (-b) / b ^ 2 := by
        ring
  have h1 : (∫ t in Set.Ioi b, Real.exp (-t) / t ^ 2) ≤
      (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) := by
    refine integral_mono_ae ?_ ?_ ?_
    · apply Integrable.mono'
      · exact ((integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)).const_mul (b⁻¹)
      · apply ContinuousOn.aestronglyMeasurable
        · apply ContinuousOn.div
          · exact (Real.continuous_exp.comp continuous_neg).continuousOn
          · exact (continuous_id.pow 2).continuousOn
          · intro x hx
            have hx0 : 0 < x := lt_trans hb hx
            exact ne_of_gt (sq_pos_of_pos hx0)
        · exact measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := lt_trans hb ht
        have htb : b ≤ t := le_of_lt ht
        have h_nonneg : 0 ≤ Real.exp (-t) := le_of_lt (Real.exp_pos (-t))
        have hnonneg2 : 0 ≤ Real.exp (-t) / t ^ 2 := by
          exact div_nonneg h_nonneg (sq_pos_of_pos ht_pos).le
        have hsq : (1 / t ^ 2 : ℝ) ≤ 1 / b ^ 2 := by
          have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht_pos
          have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
          exact (one_div_le_one_div ht2 hb2).2 (pow_le_pow_left₀ (le_of_lt hb) htb 2)
        have hsq' : (t ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ := by
          simpa [one_div] using hsq
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg hnonneg2]
        calc
          Real.exp (-t) / t ^ 2 = Real.exp (-t) * (t ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
          _ ≤ Real.exp (-t) * (b ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hsq' h_nonneg
          _ = b⁻¹ * (b⁻¹ * Real.exp (-t)) := by
            ring
    · exact ((integrableOn_exp_neg_Ioi b).const_mul (b⁻¹)).const_mul (b⁻¹)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := lt_trans hb ht
      have htb : b ≤ t := le_of_lt ht
      have h_nonneg : 0 ≤ Real.exp (-t) := le_of_lt (Real.exp_pos (-t))
      have hsq : (1 / t ^ 2 : ℝ) ≤ 1 / b ^ 2 := by
        have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht_pos
        have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
        exact (one_div_le_one_div ht2 hb2).2 (pow_le_pow_left₀ (le_of_lt hb) htb 2)
      have hsq' : (t ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ := by
        simpa [one_div] using hsq
      calc
        Real.exp (-t) / t ^ 2 = Real.exp (-t) * (t ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
        _ ≤ Real.exp (-t) * (b ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hsq' h_nonneg
        _ = b⁻¹ * (b⁻¹ * Real.exp (-t)) := by
          ring
  calc
    (∫ t in Set.Ioi b, Real.exp (-t) / t ^ 2) ≤
        (∫ t in Set.Ioi b, b⁻¹ * (b⁻¹ * Real.exp (-t))) := h1
    _ = Real.exp (-b) / b ^ 2 := hg

end
