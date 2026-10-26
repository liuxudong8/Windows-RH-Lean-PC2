import QRH.S7_1_Stage3
open Real
noncomputable section

/-- 三角不等式 |a+b| ≤ |a|+|b|（本地自证，避开未编译模块）。 -/
private lemma abs_add_ineq (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · linarith [neg_le_abs a, neg_le_abs b]
  · linarith [le_abs_self a, le_abs_self b]

namespace QRH

/-- √2 ≥ q（q ≥ 0，q² ≤ 2）。 -/
lemma sqrt2_ge (q : ℝ) (hq0 : 0 ≤ q) (hq : q ^ 2 ≤ 2) : q ≤ sqrt 2 := by
  have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : q ^ 2 ≤ (sqrt 2) ^ 2 := by simpa [h2] using hq
  have habs : |q| ≤ |sqrt 2| := (sq_le_sq.mp hsq)
  have hqabs : |q| = q := abs_of_nonneg hq0
  have hsq2abs : |sqrt 2| = sqrt 2 := abs_of_nonneg (by positivity)
  simpa [hqabs, hsq2abs] using habs

/-- √2 ≤ q（q ≥ 0，2 ≤ q²）。 -/
lemma sqrt2_le (q : ℝ) (hq0 : 0 ≤ q) (hq : 2 ≤ q ^ 2) : sqrt 2 ≤ q := by
  have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : (sqrt 2) ^ 2 ≤ q ^ 2 := by simpa [h2] using hq
  have habs : |sqrt 2| ≤ |q| := (sq_le_sq.mp hsq)
  have hqabs : |q| = q := abs_of_nonneg hq0
  have hsq2abs : |sqrt 2| = sqrt 2 := abs_of_nonneg (by positivity)
  simpa [hqabs, hsq2abs] using habs

/-- cos 在 [0, π] 上递减（自证：cos x = sin(π/2 − x)，sin 在 [−π/2, π/2] 递增）。 -/
lemma cos_dec_on (x y : ℝ) (hxy : x ≤ y) (hx0 : 0 ≤ x) (hypi : y ≤ Real.pi) :
    cos y ≤ cos x := by
  have htmp' : ∀ t : ℝ, cos (Real.pi / 2 - t) = sin t := by
    intro t
    rw [Real.cos_sub]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have h2 : cos (Real.pi / 2 - (Real.pi / 2 - x)) = sin (Real.pi / 2 - x) :=
    htmp' (Real.pi / 2 - x)
  have hcosx : cos x = sin (Real.pi / 2 - x) := by
    convert h2 using 1
    ring_nf
  have h3 : cos (Real.pi / 2 - (Real.pi / 2 - y)) = sin (Real.pi / 2 - y) :=
    htmp' (Real.pi / 2 - y)
  have hcosy : cos y = sin (Real.pi / 2 - y) := by
    convert h3 using 1
    ring_nf
  rw [hcosx, hcosy]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have : -(Real.pi / 2) ≤ Real.pi / 2 - y := by linarith [hypi]
    exact this
  · have : Real.pi / 2 - x ≤ Real.pi / 2 := by linarith [hx0]
    exact this
  · linarith [hxy]

/-- cos(8/5) < 0（cos 1.6 = 2cos²0.8 − 1；cos_bound 给出 cos 0.8 ≤ 3507/5000）。 -/
lemma cos_8_div_5_lt : cos (8 / 5) < 0 := by
  have hb : |(4 : ℝ) / 5| ≤ 1 := by norm_num
  have hcb := Real.cos_bound (x := (4 : ℝ) / 5) hb
  have hc : cos (4 / 5) ≤ 3507 / 5000 := by
    have hcb2 : cos (4 / 5) - (1 - (4 / 5) ^ 2 / 2) ≤ (4 / 5) ^ 4 * (5 / 96) := by
      simpa [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)] using (abs_le.mp hcb).2
    have : cos (4 / 5) ≤ 1 - (4 / 5) ^ 2 / 2 + (4 / 5) ^ 4 * 5 / 96 := by
      linarith
    nlinarith
  have hcosnonneg : 0 ≤ cos (4 / 5) := by
    exact le_of_lt (Real.cos_pos_of_mem_Ioo (by
      constructor
      · have : -(Real.pi / 2) < (4 : ℝ) / 5 := by linarith [two_le_pi]
        exact this
      · have : (4 : ℝ) / 5 < Real.pi / 2 := by linarith [two_le_pi]
        exact this))
  have hcsq : cos (4 / 5) ^ 2 ≤ (3507 / 5000) ^ 2 := by
    have habs : |cos (4 / 5)| ≤ |3507 / 5000| := by
      simpa [abs_of_nonneg hcosnonneg, abs_of_pos (by norm_num : (0 : ℝ) < 3507 / 5000)]
        using hc
    exact sq_le_sq.mpr habs
  rw [show (8 : ℝ) / 5 = 2 * ((4 : ℝ) / 5) by norm_num]
  rw [Real.cos_two_mul]
  nlinarith

/-- π < 16/5（=3.2）：π/2 ≥ 8/5 则 cos 递减 ⟹ 0 ≤ cos(8/5)，与 cos(8/5)<0 矛盾。 -/
lemma pi_lt_32 : Real.pi < 16 / 5 := by
  by_contra h
  have hge : 16 / 5 ≤ Real.pi := le_of_not_gt h
  have hhalf : (8 : ℝ) / 5 ≤ Real.pi / 2 := by linarith
  have hdec : cos (Real.pi / 2) ≤ cos (8 / 5) :=
    cos_dec_on (8 / 5) (Real.pi / 2) hhalf (by norm_num) (by linarith [hge])
  rw [Real.cos_pi_div_two] at hdec
  have hcoslt : cos (8 / 5) < 0 := cos_8_div_5_lt
  linarith

/-- √2/2 = 1/√2。 -/
lemma sqrt2_div_two_eq_inv : sqrt 2 / 2 = 1 / sqrt 2 := by
  field_simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  all_goals try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- 14141/10000 ≤ √2。 -/
lemma sqrt2_14141 : (14141 : ℝ) / 10000 ≤ sqrt 2 :=
  sqrt2_ge (14141 / 10000) (by norm_num) (by norm_num : ((14141 : ℝ) / 10000) ^ 2 ≤ 2)

/-- √2 ≤ 14143/10000。 -/
lemma sqrt2_le_14143 : sqrt 2 ≤ (14143 : ℝ) / 10000 :=
  sqrt2_le (14143 / 10000) (by norm_num) (by norm_num : 2 ≤ ((14143 : ℝ) / 10000) ^ 2)

/-- |1/√2| ≤ 1。 -/
lemma inv_sqrt2_abs_le_one : |1 / sqrt 2| ≤ 1 := by
  have h1 : (1 : ℝ) ≤ sqrt 2 := sqrt2_ge 1 (by norm_num) (by norm_num : (1 : ℝ) ^ 2 ≤ 2)
  have hbb : 1 / sqrt 2 ≤ 1 / (1 : ℝ) :=
    (one_div_le_one_div (by positivity : (0 : ℝ) < sqrt 2) (by norm_num : (0 : ℝ) < 1)).mpr h1
  have hb' : 1 / sqrt 2 ≤ 1 := by simpa using hbb
  have hnn : 0 ≤ 1 / sqrt 2 := by positivity
  rwa [abs_of_nonneg hnn]

/-- 10000/14143 ≤ 1/√2 ≤ 10000/14141。 -/
lemma inv_sqrt2_bounds :
    10000 / 14143 ≤ 1 / sqrt 2 ∧ 1 / sqrt 2 ≤ 10000 / 14141 := by
  constructor
  · -- 1/(14143/10000) ≤ 1/√2 ↔ √2 ≤ 14143/10000
    have hb : 1 / (14143 / 10000) ≤ 1 / sqrt 2 :=
      (one_div_le_one_div (by norm_num : (0 : ℝ) < 14143 / 10000)
        (by positivity : (0 : ℝ) < sqrt 2)).mpr sqrt2_le_14143
    -- 1/(14143/10000) = 10000/14143
    simpa using hb
  · -- 1/√2 ≤ 1/(14141/10000) ↔ 14141/10000 ≤ √2
    have hb : 1 / sqrt 2 ≤ 1 / (14141 / 10000) :=
      (one_div_le_one_div (by positivity : (0 : ℝ) < sqrt 2)
        (by norm_num : (0 : ℝ) < 14141 / 10000)).mpr sqrt2_14141
    -- 1/(14141/10000) = 10000/14141
    simpa using hb

/-- sin(1/√2) ≥ 323/500（sin_bound 三阶下界 + 1/√2 区间）。 -/
lemma sin_inv_sqrt2_ge : sin (1 / sqrt 2) ≥ 323 / 500 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.sin_bound (x := 1 / sqrt 2) hb0
  -- sin x ≥ x − x³/6 − |x|⁵/100
  have hl : sin (1 / sqrt 2) ≥ (1 / sqrt 2) - (1 / sqrt 2) ^ 3 / 6 - |1 / sqrt 2| ^ 5 / 100 := by
    have h1 := (abs_le.mp hb).1
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx5 : |1 / sqrt 2| ^ 5 = (1 / sqrt 2) ^ 5 := by rw [abs_of_nonneg hx]
  rw [hx5] at hl
  have h1 : (1 / sqrt 2) ^ 3 ≤ (10000 / 14141) ^ 3 := pow_le_pow_left₀ hx hib 3
  have h2 : (1 / sqrt 2) ^ 5 ≤ (10000 / 14141) ^ 5 := pow_le_pow_left₀ hx hib 5
  have h3 : (10000 / 14143 : ℝ) ≤ 1 / sqrt 2 := hia
  have hnum : 10000 / 14143 - (10000 / 14141) ^ 3 / 6 - (10000 / 14141) ^ 5 / 100 ≥ 323 / 500 := by
    norm_num
  linarith

/-- sin(1/√2) ≤ 651/1000（sin_bound 三阶上界 + 1/√2 区间）。 -/
lemma sin_inv_sqrt2_le : sin (1 / sqrt 2) ≤ 651 / 1000 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.sin_bound (x := 1 / sqrt 2) hb0
  have hl : sin (1 / sqrt 2) ≤ (1 / sqrt 2) - (1 / sqrt 2) ^ 3 / 6 + |1 / sqrt 2| ^ 5 / 100 := by
    have h1 := (abs_le.mp hb).2
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx5 : |1 / sqrt 2| ^ 5 = (1 / sqrt 2) ^ 5 := by rw [abs_of_nonneg hx]
  rw [hx5] at hl
  have h1 : (10000 / 14143) ^ 3 ≤ (1 / sqrt 2) ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 14143) hia 3
  have h2 : (1 / sqrt 2) ^ 5 ≤ (10000 / 14141) ^ 5 := pow_le_pow_left₀ hx hib 5
  have hnum : 10000 / 14141 - (10000 / 14143) ^ 3 / 6 + (10000 / 14141) ^ 5 / 100 ≤ 651 / 1000 := by
    norm_num
  linarith

/-- cos(1/√2) ≥ 736/1000（cos_bound 二阶下界 + 1/√2 区间）。 -/
lemma cos_inv_sqrt2_ge : cos (1 / sqrt 2) ≥ 736 / 1000 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.cos_bound (x := 1 / sqrt 2) hb0
  have hl : cos (1 / sqrt 2) ≥ 1 - (1 / sqrt 2) ^ 2 / 2 - |1 / sqrt 2| ^ 4 * (5 / 96) := by
    have h1 := (abs_le.mp hb).1
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx4 : |1 / sqrt 2| ^ 4 = (1 / sqrt 2) ^ 4 := by rw [abs_of_nonneg hx]
  rw [hx4] at hl
  have h1 : (1 / sqrt 2) ^ 2 ≤ (10000 / 14141) ^ 2 := pow_le_pow_left₀ hx hib 2
  have h2 : (1 / sqrt 2) ^ 4 ≤ (10000 / 14141) ^ 4 := pow_le_pow_left₀ hx hib 4
  have hnum : 1 - (10000 / 14141) ^ 2 / 2 - (10000 / 14141) ^ 4 * (5 / 96) ≥ 736 / 1000 := by
    norm_num
  linarith

/-- cos(1/√2) ≤ 7631/10000（cos_bound 二阶上界 + 1/√2 区间）。 -/
lemma cos_inv_sqrt2_le : cos (1 / sqrt 2) ≤ 7631 / 10000 := by
  have hb0 : |1 / sqrt 2| ≤ 1 := inv_sqrt2_abs_le_one
  have hb := Real.cos_bound (x := 1 / sqrt 2) hb0
  have hl : cos (1 / sqrt 2) ≤ 1 - (1 / sqrt 2) ^ 2 / 2 + |1 / sqrt 2| ^ 4 * (5 / 96) := by
    have h1 := (abs_le.mp hb).2
    nlinarith
  have hia := inv_sqrt2_bounds.1
  have hib := inv_sqrt2_bounds.2
  have hx : 0 ≤ 1 / sqrt 2 := by positivity
  have hx4 : |1 / sqrt 2| ^ 4 = (1 / sqrt 2) ^ 4 := by rw [abs_of_nonneg hx]
  rw [hx4] at hl
  have h1sq : (10000 / 14143) ^ 2 ≤ (1 / sqrt 2) ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 14143) hia 2
  have h2p4 : (1 / sqrt 2) ^ 4 ≤ (10000 / 14141) ^ 4 := pow_le_pow_left₀ hx hib 4
  have hnum : (1 : ℝ) - ((10000 : ℝ) / 14143) ^ 2 / 2 + ((10000 : ℝ) / 14141) ^ 4 * (5 / 96)
      ≤ 7631 / 10000 := by
    have hna : ((10000 : ℝ) / 14143) ^ 2 ≥ 12497 / 25000 := by norm_num
    have hnb : ((10000 : ℝ) / 14141) ^ 4 ≤ 25012 / 100000 := by norm_num
    have hpart1 : ((10000 : ℝ) / 14143) ^ 2 / 2 ≥ 12497 / 50000 := by
      have h1 : (12497 / 25000) / 2 ≤ ((10000 : ℝ) / 14143) ^ 2 / 2 :=
        div_le_div_of_nonneg_right hna (by norm_num : (0 : ℝ) ≤ 2)
      have hnumv : (12497 / 25000 : ℝ) / 2 = 12497 / 50000 := by norm_num
      rwa [hnumv] at h1
    have hpart2 : ((10000 : ℝ) / 14141) ^ 4 * (5 / 96) ≤ 6253 / 480000 := by
      have h1 : ((10000 : ℝ) / 14141) ^ 4 * (5 / 96) ≤ (25012 / 100000) * (5 / 96) :=
        mul_le_mul_of_nonneg_right hnb (by norm_num : (0 : ℝ) ≤ 5 / 96)
      have hnumv : (25012 / 100000 : ℝ) * (5 / 96) = 6253 / 480000 := by norm_num
      rwa [hnumv] at h1
    have hnum2 : 37503 / 50000 + 6253 / 480000 ≤ 7631 / 10000 := by norm_num
    have h1 : (12497 : ℝ) / 50000 ≤ (10000 / 14143) ^ 2 / 2 := by linarith [hpart1]
    have hone : (12497 : ℝ) / 50000 + 37503 / 50000 = 1 := by norm_num
    have hstepA : (1 : ℝ) - ((10000 : ℝ) / 14143) ^ 2 / 2 ≤ 37503 / 50000 := by
      linarith [h1, hone]
    have hstep : (1 : ℝ) - ((10000 : ℝ) / 14143) ^ 2 / 2 + ((10000 : ℝ) / 14141) ^ 4 * (5 / 96)
        ≤ 37503 / 50000 + 6253 / 480000 := by
      linarith [h1, hone, hpart2]
    linarith [hstep, hnum2]
  nlinarith [hl, h1sq, h2p4, hnum]

/-- 1 ≤ cotR(√2/2) ≤ 237/200。 -/
lemma cotR_half_bounds : 1 ≤ cotR (sqrt 2 / 2) ∧ cotR (sqrt 2 / 2) ≤ 237 / 200 := by
  unfold cotR
  rw [sqrt2_div_two_eq_inv]
  have hsin : 0 < sin (1 / sqrt 2) := by linarith [sin_inv_sqrt2_ge]
  constructor
  · -- cot ≥ 1 ⟸ cos ≥ sin
    have hcos : (736 : ℝ) / 1000 ≤ cos (1 / sqrt 2) := cos_inv_sqrt2_ge
    have hsinu : sin (1 / sqrt 2) ≤ 651 / 1000 := sin_inv_sqrt2_le
    have hcs : cos (1 / sqrt 2) ≥ sin (1 / sqrt 2) := by linarith
    -- (cos−sin)/sin = cos/sin − 1 ≥ 0
    have hnum : 0 ≤ cos (1 / sqrt 2) - sin (1 / sqrt 2) := by linarith
    have hfrac : 0 ≤ (cos (1 / sqrt 2) - sin (1 / sqrt 2)) / sin (1 / sqrt 2) :=
      div_nonneg hnum (le_of_lt hsin)
    have hrewrite : (cos (1 / sqrt 2) - sin (1 / sqrt 2)) / sin (1 / sqrt 2)
        = cos (1 / sqrt 2) / sin (1 / sqrt 2) - 1 := by
      field_simp [ne_of_gt hsin]
    rw [hrewrite] at hfrac
    linarith
  · -- cot ≤ 237/200：cos/sin ≤ (7631/10000)/(323/500)
    have hcos : cos (1 / sqrt 2) ≤ 7631 / 10000 := cos_inv_sqrt2_le
    have hsinu : (323 : ℝ) / 500 ≤ sin (1 / sqrt 2) := sin_inv_sqrt2_ge
    -- 1/sin ≤ 500/323（hsinu：倒数递减）
    have hinv : (sin (1 / sqrt 2))⁻¹ ≤ 500 / 323 := by
      have hb : 1 / sin (1 / sqrt 2) ≤ 1 / (323 / 500) :=
        (one_div_le_one_div hsin (by norm_num : (0 : ℝ) < 323 / 500)).mpr hsinu
      simpa [one_div] using hb
    have hcosn : 0 ≤ cos (1 / sqrt 2) := by linarith [cos_inv_sqrt2_ge]
    have hprod : cos (1 / sqrt 2) * (sin (1 / sqrt 2))⁻¹ ≤ 7631 / 10000 * (500 / 323) := by
      exact mul_le_mul hcos hinv (inv_nonneg.mpr (le_of_lt hsin))
        (by norm_num : (0 : ℝ) ≤ 7631 / 10000)
    have hnum : 7631 / 10000 * (500 / 323) ≤ 237 / 200 := by norm_num
    have hrewrite : cos (1 / sqrt 2) / sin (1 / sqrt 2) = cos (1 / sqrt 2) * (sin (1 / sqrt 2))⁻¹ := by
      rw [div_eq_mul_inv]
    rw [hrewrite]
    linarith

/-- |3/2 − √2·cotR(√2/2)| ≤ 9/50。 -/
lemma c0_bound : |(3 : ℝ) / 2 - sqrt 2 * cotR (sqrt 2 / 2)| ≤ 9 / 50 := by
  have hcot1 : 1 ≤ cotR (sqrt 2 / 2) := cotR_half_bounds.1
  have hcot2 : cotR (sqrt 2 / 2) ≤ 237 / 200 := cotR_half_bounds.2
  have hsqrtn : 0 ≤ sqrt 2 := by positivity
  have hup : (3 : ℝ) / 2 - sqrt 2 * cotR (sqrt 2 / 2) ≤ 9 / 50 := by
    have h1 : sqrt 2 * 1 ≤ sqrt 2 * cotR (sqrt 2 / 2) :=
      mul_le_mul_of_nonneg_left hcot1 hsqrtn
    have hlo : (14141 : ℝ) / 10000 ≤ sqrt 2 := sqrt2_14141
    linarith
  have hlo : -(9 / 50) ≤ (3 : ℝ) / 2 - sqrt 2 * cotR (sqrt 2 / 2) := by
    have hsqrt2 : sqrt 2 ≤ 14143 / 10000 := sqrt2_le_14143
    have hcotn : 0 ≤ cotR (sqrt 2 / 2) := by linarith [hcot1]
    have hprod : sqrt 2 * cotR (sqrt 2 / 2) ≤ 14143 / 10000 * (237 / 200) :=
      mul_le_mul hsqrt2 hcot2 hcotn (by norm_num : (0 : ℝ) ≤ 14143 / 10000)
    have hnum : 14143 / 10000 * (237 / 200) ≤ (3 : ℝ) / 2 + 9 / 50 := by norm_num
    nlinarith
  exact abs_le.mpr ⟨hlo, hup⟩

/-- 闭式（乘形式）：K̂(u)·(1 − 2π²u²) = cos(πu) − √2πu·cotR(√2/2)·sin(πu)，|u| ≤ 1/24 域内。 -/
lemma Khat_closed_form (u : ℝ) (hu : |u| ≤ (1 : ℝ) / 24) :
    Khat u * (1 - 2 * (Real.pi * u) ^ 2)
      = cos (Real.pi * u) - sqrt 2 * Real.pi * u * cotR (sqrt 2 / 2) * sin (Real.pi * u) := by
  unfold Khat cotR
  have hpi : Real.pi ≤ 4 := by linarith [pi_lt_32]
  have hpi_nonneg : 0 ≤ Real.pi := le_of_lt pi_pos
  have hpu2 : Real.pi * |u| ≤ 1 / 6 := by
    calc
      Real.pi * |u| ≤ 4 * (1 / 24) := by
        exact mul_le_mul hpi hu (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 4)
      _ = 1 / 6 := by norm_num
  have hpu : |Real.pi * u| ≤ 1 / 6 := by
    calc
      |Real.pi * u| = Real.pi * |u| := by rw [abs_mul, abs_of_pos pi_pos]
      _ ≤ 1 / 6 := hpu2
  have hb2 : 2 * Real.pi * |u| ≤ 1 / 3 := by
    calc
      2 * Real.pi * |u| = 2 * (Real.pi * |u|) := by ring
      _ ≤ 2 * (1 / 6) := by exact mul_le_mul_of_nonneg_left hpu2 (by norm_num)
      _ = 1 / 3 := by norm_num
  have hlo : (0 : ℝ) < sqrt 2 - 1 / 3 := by
    have h43 : (4 : ℝ) / 3 ≤ sqrt 2 :=
      sqrt2_ge (4 / 3) (by norm_num) (by norm_num : ((4 : ℝ) / 3) ^ 2 ≤ 2)
    linarith
  have hd1 : sqrt 2 - 2 * Real.pi * u ≠ 0 := by
    have h2u : 2 * Real.pi * u ≤ 2 * Real.pi * |u| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self u) (mul_nonneg (by norm_num) hpi_nonneg)
    have : 0 < sqrt 2 - 2 * Real.pi * u := by linarith
    exact ne_of_gt this
  have hd2 : sqrt 2 + 2 * Real.pi * u ≠ 0 := by
    have hc : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hpi_nonneg
    have hneg : -u ≤ |u| := neg_le_abs u
    have h2u : -(2 * Real.pi * u) ≤ 2 * Real.pi * |u| := by
      calc
        -(2 * Real.pi * u) = (2 * Real.pi) * (-u) := by ring
        _ ≤ (2 * Real.pi) * |u| := mul_le_mul_of_nonneg_left hneg hc
    have : 0 < sqrt 2 + 2 * Real.pi * u := by linarith
    exact ne_of_gt this
  -- 1−2m² = (√2−2πu)(√2+2πu)/2
  have hmain : (1 : ℝ) - 2 * (Real.pi * u) ^ 2
      = (sqrt 2 - 2 * Real.pi * u) * (sqrt 2 + 2 * Real.pi * u) / 2 := by
    ring_nf
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  rw [hmain]
  field_simp [hd1, hd2, sin_inv_sqrt2_ne_zero]
  have hA : (sqrt 2 - 2 * Real.pi * u) / 2 = sqrt 2 / 2 - Real.pi * u := by ring
  have hB : (sqrt 2 + 2 * Real.pi * u) / 2 = sqrt 2 / 2 + Real.pi * u := by ring
  rw [hA, hB]
  rw [Real.sin_sub, Real.sin_add]
  rw [sqrt2_div_two_eq_inv]
  have hs0 : sin (sqrt 2)⁻¹ ≠ 0 := by
    simpa [one_div] using sin_inv_sqrt2_ne_zero
  field_simp [hd1, hd2, hs0]
  ring_nf
  have hsq : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hsq]
  ring_nf

/-- |K̂(u)−1| ≤ 2u²+u⁴ 在 |u| ≤ 1/24 域（Taylor 二阶余项 + cotR 数值区间 + π < 16/5）。 -/
lemma khat_second_order_bound_dbg :
    BoundBall 1 (1 / 24) (fun x => |Khat x - 1|) (fun x => 2 * x ^ 2 + x ^ 4) := by
  unfold BoundBall
  constructor
  · norm_num
  · intro u hu
    let m : ℝ := Real.pi * u
    have hpi : Real.pi ≤ 16 / 5 := le_of_lt pi_lt_32
    have hm : |m| ≤ 2 / 15 := by
      dsimp [m]
      calc
        |Real.pi * u| = Real.pi * |u| := by rw [abs_mul, abs_of_pos pi_pos]
        _ ≤ (16 / 5) * (1 / 24) := by
          exact mul_le_mul hpi hu (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 16 / 5)
        _ = 2 / 15 := by norm_num
    have hm2 : m ^ 2 ≤ 4 / 225 := by
      have habs : |m| ≤ |(2 : ℝ) / 15| := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 15)]
        exact hm
      calc
        m ^ 2 ≤ (2 / 15) ^ 2 := sq_le_sq.mpr habs
        _ = 4 / 225 := by norm_num
    have hm2nonneg : 0 ≤ m ^ 2 := sq_nonneg m
    have hden_ge : (1 : ℝ) - 2 * m ^ 2 ≥ 217 / 225 := by nlinarith [hm2]
    have hden_pos : 0 < 1 - 2 * m ^ 2 := by linarith [hden_ge]
    have hden_ne : (1 : ℝ) - 2 * m ^ 2 ≠ 0 := ne_of_gt hden_pos
    have hm1 : |m| ≤ 1 := by linarith [hm]
    -- 闭式
    have hcf := Khat_closed_form u hu
    have hK : Khat u = (cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m) / (1 - 2 * m ^ 2) := by
      have hd : (1 : ℝ) - 2 * (Real.pi * u) ^ 2 ≠ 0 := by
        dsimp [m] at hden_ne
        exact hden_ne
      have hcf' : Khat u = (cos (Real.pi * u) - sqrt 2 * (Real.pi * u) * cotR (sqrt 2 / 2)
          * sin (Real.pi * u)) / (1 - 2 * (Real.pi * u) ^ 2) := by
        calc
          Khat u = (Khat u * (1 - 2 * (Real.pi * u) ^ 2)) / (1 - 2 * (Real.pi * u) ^ 2) := by
            rw [div_eq_mul_inv]
            rw [mul_assoc]
            rw [mul_inv_cancel₀ hd]
            ring
          _ = (cos (Real.pi * u) - sqrt 2 * (Real.pi * u) * cotR (sqrt 2 / 2)
              * sin (Real.pi * u)) / (1 - 2 * (Real.pi * u) ^ 2) := by
            rw [hcf]
            ring_nf
      dsimp [m]
      convert hcf' using 1
    have hden_ne2 : (1 : ℝ) - m ^ 2 * 2 ≠ 0 := by
      convert hden_ne using 1
      ring
    -- |K̂u−1| = |N|/(1−2m²)
    have hN_abs : |Khat u - 1|
        = |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2) := by
      calc
        |Khat u - 1| = |(cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m) / (1 - 2 * m ^ 2) - 1| := by rw [hK]
        _ = |(cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m - (1 - 2 * m ^ 2)) / (1 - 2 * m ^ 2)| := by
          congr 1
          field_simp [hden_ne2]
        _ = |cos m - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m - (1 - 2 * m ^ 2)| / (1 - 2 * m ^ 2) := by
          rw [abs_div]
          rw [abs_of_pos hden_pos]
        _ = |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2) := by
          congr 1
          ring
    -- rc：cos 二阶余项
    have hrc : |cos m - (1 - m ^ 2 / 2)| ≤ m ^ 4 * (5 / 96) := by
      have hcb := Real.cos_bound (x := m) hm1
      have htmp : |m| ^ 4 = m ^ 4 := by
        rw [← abs_pow]
        exact abs_of_nonneg (by rw [show m ^ 4 = (m ^ 2) ^ 2 by ring]; exact sq_nonneg (m ^ 2))
      simpa [htmp] using hcb
    -- rs：sin 一阶余项
    have hrs : |sin m - m| ≤ |m| ^ 5 / 100 + |m| ^ 3 / 6 := by
      have hsb := Real.sin_bound (x := m) hm1
      calc
        |sin m - m| = |(sin m - (m - m ^ 3 / 6)) + (-(m ^ 3 / 6))| := by congr 1; ring
        _ ≤ |sin m - (m - m ^ 3 / 6)| + |-(m ^ 3 / 6)| := by
          simpa using abs_add_ineq (sin m - (m - m ^ 3 / 6)) (-(m ^ 3 / 6))
        _ = |sin m - (m - m ^ 3 / 6)| + |m ^ 3 / 6| := by rw [abs_neg]
        _ ≤ |m| ^ 5 / 100 + |m| ^ 3 / 6 := by
          have h2 : |m ^ 3 / 6| = |m| ^ 3 / 6 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
            rw [abs_pow]
          rw [h2]
          linarith [hsb]
    -- A 项
    have hA : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2| ≤ (9 / 50) * m ^ 2 := by
      calc
        |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2|
            = |3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)| * |m ^ 2| := by rw [abs_mul]
        _ = |3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)| * m ^ 2 := by rw [abs_of_nonneg hm2nonneg]
        _ ≤ (9 / 50) * m ^ 2 := mul_le_mul_of_nonneg_right c0_bound hm2nonneg
    -- |m|⁴ = m⁴、|m|⁶ ≤ m⁴
    have hm4eq : |m| ^ 4 = m ^ 4 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by rw [show m ^ 4 = (m ^ 2) ^ 2 by ring]; exact sq_nonneg (m ^ 2))
    have hm6le : |m| ^ 6 ≤ m ^ 4 := by
      have hmm2 : |m| ^ 2 ≤ 1 := by nlinarith [hm]
      have hmp : 0 ≤ |m| ^ 4 := pow_nonneg (abs_nonneg m) 4
      calc
        |m| ^ 6 = |m| ^ 4 * |m| ^ 2 := by rw [← pow_add]
        _ ≤ |m| ^ 4 * 1 := mul_le_mul_of_nonneg_left hmm2 hmp
        _ = |m| ^ 4 := by simp
        _ = m ^ 4 := hm4eq
    -- B 项：|√2 m cotR (sin m − m)|
    have hB1 : |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
        ≤ sqrt 2 * |m| * cotR (sqrt 2 / 2) * |sin m - m| := by
      rw [abs_mul, abs_mul, abs_mul]
      rw [abs_of_nonneg (by positivity : 0 ≤ sqrt 2)]
      rw [abs_of_nonneg (by linarith [cotR_half_bounds.1] : 0 ≤ cotR (sqrt 2 / 2))]
    have hsq15 : sqrt 2 ≤ 3 / 2 := sqrt2_le (3 / 2 : ℝ) (by norm_num) (by norm_num : 2 ≤ (3 / 2 : ℝ) ^ 2)
    have hcotle : cotR (sqrt 2 / 2) ≤ 237 / 200 := cotR_half_bounds.2
    have hA2 : sqrt 2 * cotR (sqrt 2 / 2) ≤ (3 / 2) * (237 / 200) :=
      mul_le_mul hsq15 hcotle (by linarith [cotR_half_bounds.1] : 0 ≤ cotR (sqrt 2 / 2))
        (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hB2 : sqrt 2 * |m| * cotR (sqrt 2 / 2) * |sin m - m|
        ≤ (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) := by
      calc
        sqrt 2 * |m| * cotR (sqrt 2 / 2) * |sin m - m|
            = (sqrt 2 * cotR (sqrt 2 / 2)) * (|m| * |sin m - m|) := by ring
        _ ≤ ((3 / 2) * (237 / 200)) * (|m| * |sin m - m|) := by
          exact mul_le_mul_of_nonneg_right hA2 (mul_nonneg (abs_nonneg m) (abs_nonneg (sin m - m)))
        _ ≤ ((3 / 2) * (237 / 200)) * (|m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)) := by
          have hmm : |m| * |sin m - m| ≤ |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) :=
            mul_le_mul_of_nonneg_left hrs (abs_nonneg m)
          exact mul_le_mul_of_nonneg_left hmm (by norm_num : (0 : ℝ) ≤ (3 / 2) * (237 / 200))
        _ = (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) := by ring
    have hB3 : (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)
        ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := by
      have hnum : (3 : ℝ) / 2 * (237 / 200) = 711 / 400 := by norm_num
      have hmm : |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6) = |m| ^ 6 / 100 + |m| ^ 4 / 6 := by
        ring
      have hsum : |m| ^ 6 / 100 + |m| ^ 4 / 6 ≤ m ^ 4 / 100 + m ^ 4 / 6 := by
        have h1 : |m| ^ 6 / 100 ≤ m ^ 4 / 100 := by
          exact div_le_div_of_nonneg_right hm6le (by norm_num : (0 : ℝ) ≤ 100)
        have h2 : |m| ^ 4 / 6 = m ^ 4 / 6 := by rw [hm4eq]
        rw [h2]
        linarith [h1]
      calc
        (3 / 2) * (237 / 200) * |m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)
            = (711 / 400) * (|m| * (|m| ^ 5 / 100 + |m| ^ 3 / 6)) := by
              rw [hnum]
              ring
        _ = (711 / 400) * (|m| ^ 6 / 100 + |m| ^ 4 / 6) := by rw [hmm]
        _ ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 711 / 400)
    have hB : |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
        ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := by
      exact le_trans (le_trans hB1 hB2) hB3
    -- N 的三角分解
    have hsplit : cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m
        = (3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
          + (cos m - (1 - m ^ 2 / 2) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)) := by
      ring
    have htri1 : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
          + (cos m - (1 - m ^ 2 / 2) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))|
        ≤ |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2| + |cos m - (1 - m ^ 2 / 2)|
          + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
      have h1 : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
            + ((cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))|
          ≤ |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2|
            + |(cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
        exact abs_add_ineq ((3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2)
          ((cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))
      have h2 : |(cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
          ≤ |cos m - (1 - m ^ 2 / 2)| + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
        calc
          |(cos m - (1 - m ^ 2 / 2)) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
              = |(cos m - (1 - m ^ 2 / 2)) + (-(sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)))| := by
                rfl
          _ ≤ |cos m - (1 - m ^ 2 / 2)| + |-(sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))| :=
            abs_add_ineq (cos m - (1 - m ^ 2 / 2)) (-(sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)))
          _ = |cos m - (1 - m ^ 2 / 2)| + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := by
            rw [abs_neg]
      linarith [h1, h2]
    have hN_le : |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m|
        ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := by
      rw [hsplit]
      have hnumc : (5 / 96 : ℝ) + 711 / 400 * (1 / 100 + 1 / 6) ≤ 367 / 1000 := by norm_num
      have hrc' : |cos m - (1 - m ^ 2 / 2)| ≤ m ^ 4 * (5 / 96) := hrc
      have hB' : |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| ≤ (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := hB
      have hpart : |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2|
            + |cos m - (1 - m ^ 2 / 2)| + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)|
          ≤ (9 / 50) * m ^ 2 + m ^ 4 * (5 / 96) + (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := by
        linarith [hA, hrc', hB']
      have hnum : (9 / 50) * m ^ 2 + m ^ 4 * (5 / 96) + (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6)
          ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := by
        nlinarith [hnumc]
      calc
        |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2
            + (cos m - (1 - m ^ 2 / 2) - sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m))|
            ≤ |(3 / 2 - sqrt 2 * cotR (sqrt 2 / 2)) * m ^ 2| + |cos m - (1 - m ^ 2 / 2)|
              + |sqrt 2 * m * cotR (sqrt 2 / 2) * (sin m - m)| := htri1
        _ ≤ (9 / 50) * m ^ 2 + m ^ 4 * (5 / 96) + (711 / 400) * (m ^ 4 / 100 + m ^ 4 / 6) := hpart
        _ ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := hnum
    -- 比例拼接
    have hstep1 : |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2)
        ≤ ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2) := by
      exact div_le_div_of_nonneg_right hN_le (le_of_lt hden_pos)
    have h1d : (1 : ℝ) / (1 - 2 * m ^ 2) ≤ 225 / 217 := by
      have hc : (0 : ℝ) ≤ 225 / 217 := by norm_num
      have hle : (1 : ℝ) ≤ (225 / 217) * (1 - 2 * m ^ 2) := by
        calc
          (225 / 217) * (1 - 2 * m ^ 2) ≥ (225 / 217) * (217 / 225) :=
            mul_le_mul_of_nonneg_left hden_ge hc
          _ = 1 := by norm_num
      exact (div_le_iff₀ hden_pos).mpr hle
    have hstep2 : ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2)
        ≤ (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) := by
      have ha : 0 ≤ (9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4 := by
        have hm4n : 0 ≤ m ^ 4 := by
          rw [show m ^ 4 = (m ^ 2) ^ 2 by ring]
          exact sq_nonneg (m ^ 2)
        nlinarith [hm2nonneg, hm4n]
      calc
        ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2)
            = ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) * (1 / (1 - 2 * m ^ 2)) := by ring
        _ ≤ ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) * (225 / 217) :=
          mul_le_mul_of_nonneg_left h1d ha
        _ = (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) := by ring
    have hm4le : m ^ 4 ≤ (4 / 225) * m ^ 2 := by
      calc
        m ^ 4 = m ^ 2 * m ^ 2 := by ring
        _ ≤ m ^ 2 * (4 / 225) := mul_le_mul_of_nonneg_left hm2 hm2nonneg
        _ = (4 / 225) * m ^ 2 := by ring
    have hstep3 : (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) ≤ (194 / 1000) * m ^ 2 := by
      have hm4le2 : (225 / 217) * (367 / 1000) * m ^ 4 ≤ (225 / 217) * (367 / 1000) * (4 / 225) * m ^ 2 := by
        calc
          (225 / 217) * (367 / 1000) * m ^ 4 = (225 / 217) * (367 / 1000) * (m ^ 4) := by ring
          _ ≤ (225 / 217) * (367 / 1000) * ((4 / 225) * m ^ 2) := by
            exact mul_le_mul_of_nonneg_left hm4le (by norm_num : (0 : ℝ) ≤ (225 / 217) * (367 / 1000))
          _ = (225 / 217) * (367 / 1000) * (4 / 225) * m ^ 2 := by ring
      have hcoef : (225 : ℝ) / 217 * (9 / 50) + (225 / 217 : ℝ) * (367 / 1000) * (4 / 225)
          ≤ 194 / 1000 := by
        norm_num
      have hle2 : ((225 / 217) * (9 / 50) + (225 / 217) * (367 / 1000) * (4 / 225)) * m ^ 2
          ≤ (194 / 1000) * m ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hm2nonneg
      calc
        (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4)
            = (225 / 217) * (9 / 50) * m ^ 2 + (225 / 217) * (367 / 1000) * m ^ 4 := by ring
        _ ≤ (225 / 217) * (9 / 50) * m ^ 2 + (225 / 217) * (367 / 1000) * (4 / 225) * m ^ 2 := by
          exact add_le_add_right hm4le2 _
        _ = ((225 / 217) * (9 / 50) + (225 / 217) * (367 / 1000) * (4 / 225)) * m ^ 2 := by ring
        _ ≤ (194 / 1000) * m ^ 2 := hle2
    have hpi2 : (194 / 1000 : ℝ) * Real.pi ^ 2 ≤ 2 := by
      have hpin : 0 ≤ Real.pi := le_of_lt pi_pos
      have hpi2le : Real.pi ^ 2 ≤ (16 / 5) ^ 2 := by
        calc
          Real.pi ^ 2 = Real.pi * Real.pi := by ring
          _ ≤ (16 / 5) * Real.pi := mul_le_mul_of_nonneg_right hpi hpin
          _ ≤ (16 / 5) * (16 / 5) := mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 16 / 5)
          _ = (16 / 5) ^ 2 := by ring
      have hc : (0 : ℝ) ≤ 194 / 1000 := by norm_num
      calc
        (194 / 1000) * Real.pi ^ 2 ≤ (194 / 1000) * (16 / 5) ^ 2 := mul_le_mul_of_nonneg_left hpi2le hc
        _ = 49664 / 25000 := by norm_num
        _ ≤ 2 := by norm_num
    have hstep4 : (194 / 1000) * m ^ 2 ≤ 2 * u ^ 2 := by
      have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
      dsimp [m]
      calc
        (194 / 1000 : ℝ) * (Real.pi * u) ^ 2 = ((194 / 1000) * Real.pi ^ 2) * u ^ 2 := by ring
        _ ≤ 2 * u ^ 2 := mul_le_mul_of_nonneg_right hpi2 hu2
    have hchain1 : |Khat u - 1| ≤ (194 / 1000) * m ^ 2 := by
      calc
        |Khat u - 1| = |cos m - 1 + 2 * m ^ 2 - sqrt 2 * m * cotR (sqrt 2 / 2) * sin m| / (1 - 2 * m ^ 2) := hN_abs
        _ ≤ ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) / (1 - 2 * m ^ 2) := hstep1
        _ ≤ (225 / 217) * ((9 / 50) * m ^ 2 + (367 / 1000) * m ^ 4) := hstep2
        _ ≤ (194 / 1000) * m ^ 2 := hstep3
    have hfin : |Khat u - 1| ≤ 2 * u ^ 2 + u ^ 4 := by
      calc
        |Khat u - 1| ≤ (194 / 1000) * m ^ 2 := hchain1
        _ ≤ 2 * u ^ 2 := hstep4
        _ ≤ 2 * u ^ 2 + u ^ 4 := by
          have hu4 : 0 ≤ u ^ 4 := by
            rw [show u ^ 4 = (u ^ 2) ^ 2 by ring]
            exact sq_nonneg (u ^ 2)
          linarith [hu4]
    simpa using hfin

end QRH
