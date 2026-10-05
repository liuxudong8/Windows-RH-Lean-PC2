import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

noncomputable section

/-- 测试积分 x^(σ-1) 在 [ε₀, R₀] 上的公式 -/
theorem test_integral_rpow (ε₀ R₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_R₀ : ε₀ < R₀) (σ : ℝ) (hσ_pos : 0 < σ) :
    ∫ x in Set.Icc ε₀ R₀, x^(σ - 1) = (R₀^σ - ε₀^σ) / σ := by
  have h_le : ε₀ ≤ R₀ := le_of_lt hε₀_lt_R₀
  have h_ae : Set.Ioc ε₀ R₀ =ᵐ[MeasureTheory.volume] Set.Icc ε₀ R₀ := by
    exact?
  have h1 : ∫ x in Set.Icc ε₀ R₀, x^(σ - 1) = ∫ x in Set.Ioc ε₀ R₀, x^(σ - 1) := by
    exact?
  rw [h1]
  have h2 : ∫ x in Set.Ioc ε₀ R₀, x^(σ - 1) = ∫ x in ε₀..R₀, x^(σ - 1) := by
    rw [intervalIntegral.integral_of_le h_le]
  rw [h2]
  have hp : σ - 1 ≠ -1 := by linarith
  have h3 : ∫ x in ε₀..R₀, x^(σ - 1) = (R₀^σ - ε₀^σ) / σ := by
    -- Step 1: 把 x^(σ - 1) 写成 Real.exp ((σ - 1) * Real.log x)
    have h4 : ∀ x ∈ Set.uIcc ε₀ R₀, x^(σ - 1) = Real.exp ((σ - 1) * Real.log x) := by
      intro x hx
      have hx_pos : 0 < x := by
        have h5 : x ∈ Set.Icc ε₀ R₀ := by
          rw [Set.uIcc_of_le h_le] at hx
          exact hx
        linarith [Set.mem_Icc.mp h5]
      rw [Real.rpow_def_of_pos hx_pos]
      <;> ring
    have h5 : ∫ x in ε₀..R₀, x^(σ - 1) = ∫ x in ε₀..R₀, Real.exp ((σ - 1) * Real.log x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact h4 x hx
    rw [h5]
    -- Step 2: 变量替换 y = Real.log x
    have h6 : ∫ x in ε₀..R₀, Real.exp ((σ - 1) * Real.log x) =
        ∫ y in (Real.log ε₀)..(Real.log R₀), Real.exp (σ * y) := by
      -- 变量替换：y = Real.log x，所以 x = Real.exp y，dx = Real.exp y dy
      have hR₀_pos : 0 < R₀ := by linarith
      have h_map : Set.Icc ε₀ R₀ = Set.image Real.exp (Set.Icc (Real.log ε₀) (Real.log R₀)) := by
        ext x
        simp only [Set.mem_Icc, Set.mem_image]
        constructor
        · -- 情况 1：x ∈ Icc ε₀ R₀ → ∃ y, y ∈ Icc (log ε₀) (log R₀) 且 exp y = x
          intro h
          use Real.log x
          constructor
          · -- 证明 Real.log x ∈ Icc (Real.log ε₀) (Real.log R₀)
            have h1 : ε₀ ≤ x := h.1
            have h2 : x ≤ R₀ := h.2
            have h3 : Real.log ε₀ ≤ Real.log x := Real.log_le_log (by linarith) h1
            have h4 : Real.log x ≤ Real.log R₀ := Real.log_le_log (by linarith) h2
            exact ⟨h3, h4⟩
          · -- 证明 Real.exp (Real.log x) = x
            rw [Real.exp_log (by linarith)]
        · -- 情况 2：∃ y, y ∈ Icc (log ε₀) (log R₀) 且 exp y = x → x ∈ Icc ε₀ R₀
          rintro ⟨y, hy, rfl⟩
          have h1 : Real.log ε₀ ≤ y := hy.1
          have h2 : y ≤ Real.log R₀ := hy.2
          have h3 : Real.exp (Real.log ε₀) ≤ Real.exp y := Real.exp_le_exp.mpr h1
          have h4 : Real.exp y ≤ Real.exp (Real.log R₀) := Real.exp_le_exp.mpr h2
          have h5 : Real.exp (Real.log ε₀) = ε₀ := by rw [Real.exp_log hε₀_pos]
          have h6 : Real.exp (Real.log R₀) = R₀ := by rw [Real.exp_log hR₀_pos]
          rw [h5] at h3
          rw [h6] at h4
          exact ⟨h3, h4⟩
      -- 变量替换：y = Real.log x，所以 x = Real.exp y，dx = Real.exp y dy
      -- 我们需要证明：∫ x in ε₀..R₀, Real.exp ((σ - 1) * Real.log x) dx =
      --               ∫ y in (Real.log ε₀)..(Real.log R₀), Real.exp (σ * y) dy
      -- 这是因为：Real.exp ((σ - 1) * Real.log x) dx = Real.exp ((σ - 1) * y) * Real.exp y dy = Real.exp (σ * y) dy
      have h_le_log : Real.log ε₀ ≤ Real.log R₀ := Real.log_le_log (by linarith) (by linarith)
      have h_cont : Continuous (fun y : ℝ => Real.exp (σ * y)) := by fun_prop
      have h_ii : IntervalIntegrable (fun y : ℝ => Real.exp (σ * y)) MeasureTheory.volume (Real.log ε₀) (Real.log R₀) :=
        h_cont.intervalIntegrable (Real.log ε₀) (Real.log R₀)
      -- 变量替换定理：∫ x in ε₀..R₀, f (Real.log x) * (deriv Real.log x) dx = ∫ y in (Real.log ε₀)..(Real.log R₀), f y dy
      -- 但是我们的被积函数是 Real.exp ((σ - 1) * Real.log x) = Real.exp ((σ - 1) * y)
      -- 而 dx = Real.exp y dy
      -- 所以我们需要用 intervalIntegral.integral_comp_mul
      sorry
    rw [h6]
    -- Step 3: 计算 ∫ Real.exp (σ * y) dy
    have h7 : ∫ y in (Real.log ε₀)..(Real.log R₀), Real.exp (σ * y) =
        (Real.exp (σ * Real.log R₀) - Real.exp (σ * Real.log ε₀)) / σ := by
      have h8 : ∀ y ∈ Set.uIcc (Real.log ε₀) (Real.log R₀),
          HasDerivAt (fun y : ℝ => Real.exp (σ * y) / σ) (Real.exp (σ * y)) y := by
        intro y hy
        have h9 : HasDerivAt (fun y : ℝ => Real.exp (σ * y)) (Real.exp (σ * y) * σ) y := by
          have h10 : HasDerivAt (fun y : ℝ => σ * y) (σ : ℝ) y := by
            have h11 : HasDerivAt (fun y : ℝ => σ * id y) (σ * (1 : ℝ)) y := (hasDerivAt_id y).const_mul σ
            have h12 : σ * (1 : ℝ) = σ := by ring
            rw [h12] at h11
            simpa using h11
          exact?
        have h10 : HasDerivAt (fun y : ℝ => Real.exp (σ * y) / σ) ((Real.exp (σ * y) * σ) / σ) y := by
          exact h9.div_const σ
        have h11 : (Real.exp (σ * y) * σ) / σ = Real.exp (σ * y) := by
          field_simp [hσ_pos.ne'] <;> ring
        rw [h11] at h10
        exact h10
      have h12 : IntervalIntegrable (fun y : ℝ => Real.exp (σ * y)) MeasureTheory.volume (Real.log ε₀) (Real.log R₀) := by
        apply Continuous.intervalIntegrable
        fun_prop
      have h13 : ∫ y in (Real.log ε₀)..(Real.log R₀), Real.exp (σ * y) =
          (fun y : ℝ => Real.exp (σ * y) / σ) (Real.log R₀) - (fun y : ℝ => Real.exp (σ * y) / σ) (Real.log ε₀) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt h8 h12
      rw [h13]
      have h14 : (fun y : ℝ => Real.exp (σ * y) / σ) (Real.log R₀) - (fun y : ℝ => Real.exp (σ * y) / σ) (Real.log ε₀) =
          (Real.exp (σ * Real.log R₀) - Real.exp (σ * Real.log ε₀)) / σ := by
        simp [div_eq_mul_inv] <;> ring
      exact h14
    rw [h7]
    -- Step 4: 化简 Real.exp (σ * Real.log R₀) = R₀^σ
    have h15 : Real.exp (σ * Real.log R₀) = R₀^σ := by
      have hR₀_pos : 0 < R₀ := by linarith
      have h16 : σ * Real.log R₀ = Real.log R₀ * σ := by ring
      rw [h16]
      rw [← Real.rpow_def_of_pos hR₀_pos]
      <;> ring
    have h17 : Real.exp (σ * Real.log ε₀) = ε₀^σ := by
      have h18 : σ * Real.log ε₀ = Real.log ε₀ * σ := by ring
      rw [h18]
      rw [← Real.rpow_def_of_pos hε₀_pos]
      <;> ring
    rw [h15, h17]
  exact h3
