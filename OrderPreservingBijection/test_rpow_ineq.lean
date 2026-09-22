import OrderPreservingBijection.BasicInfrastructure
import OrderPreservingBijection.MellinInfrastructure
import OrderPreservingBijection.MollifiedFunction

open OrderPreservingBijection

noncomputable section

/-- 测试线性函数是凸函数 -/
theorem test_linear_convex (t : ℝ) :
    ConvexOn ℝ Set.univ (fun σ : ℝ => σ * t) := by
  have h : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  let f : ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun x => x * t
      map_add' := by intro x y; ring
      map_smul' := by intro c x; simp [mul_assoc, mul_comm, mul_left_comm] <;> ring }
  exact f.convexOn h

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

/-- 测试 rpow 不等式 -/
theorem test_rpow_ineq (X : ℝ) (hX_pos : 1 < X) (σ : ℝ) (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1) :
    (X^σ - 1) / σ ≤ max (Real.log X) (X - 1) := by
  -- 变量替换：令 t = Real.log X
  set t : ℝ := Real.log X with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]
    exact Real.log_pos hX_pos
  -- X = e^t
  have hX_eq : X = Real.exp t := by
    rw [ht_def]
    rw [Real.exp_log (by linarith)]
  -- X^σ = e^{σ t}
  have h1 : X^σ = Real.exp (σ * t) := by
    rw [hX_eq]
    rw [← Real.exp_mul]
    <;> ring
  rw [h1]
  -- 现在我们需要证明：
  -- (Real.exp (σ * t) - 1) / σ ≤ max t (Real.exp t - 1)
  -- 其中 t > 0，0 < σ < 1
  -- 思路：分两种情况！
  by_cases h : t ≥ Real.exp t - 1
  · -- 情况 1：t ≥ Real.exp t - 1
    -- 我们需要证明 (Real.exp (σ * t) - 1) / σ ≤ t
    -- 我们已经证明了 (Real.exp (σ * t) - 1) / σ ≤ Real.exp t - 1
    -- 而在情况 1 中，我们有 t ≥ Real.exp t - 1
    -- 所以 (Real.exp (σ * t) - 1) / σ ≤ Real.exp t - 1 ≤ t
    have h_g_nonpos : Real.exp (σ * t) - 1 - σ * (Real.exp t - 1) ≤ 0 := by
      have h21 : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) := by
        have h1 : ConvexOn ℝ Set.univ (fun σ : ℝ => Real.exp (σ * t)) :=
          test_exp_linear_convex t
        have h2 : ConvexOn ℝ Set.univ (fun σ : ℝ => σ * (-(Real.exp t - 1))) :=
          test_linear_convex (-(Real.exp t - 1))
        have h3 : ConvexOn ℝ Set.univ (fun _ : ℝ => (-1 : ℝ)) :=
          convexOn_const (-1) convex_univ
        have h_sum : ConvexOn ℝ Set.univ
            (fun σ : ℝ => Real.exp (σ * t) + σ * (-(Real.exp t - 1)) + (-1)) :=
          (h1.add h2).add h3
        have h_g_convex_univ : ConvexOn ℝ Set.univ
            (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) := by
          convert h_sum using 1
          ext σ
          ring
        have h_convex_Icc : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
        have h_subset : (Set.Icc (0:ℝ) 1) ⊆ Set.univ := by
          exact Set.subset_univ (Set.Icc (0:ℝ) 1)
        exact h_g_convex_univ.subset h_subset h_convex_Icc
      have h22 : (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 0 = 0 := by
        simp <;> ring
      have h23 : (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 1 = 0 := by
        simp <;> ring
      have h2 : ∀ σ ∈ Set.Icc (0 : ℝ) 1, Real.exp (σ * t) - 1 - σ * (Real.exp t - 1) ≤ 0 := by
        intro σ hσ
        have h_a_nonneg : 0 ≤ 1 - σ := by exact sub_nonneg.mpr hσ.2
        have h_b_nonneg : 0 ≤ σ := by exact hσ.1
        have h_sum_one : (1 - σ) + σ = 1 := by ring
        have h0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.mem_Icc]
        have h1_in : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.mem_Icc]
        have h_main : (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) σ ≤
            (1 - σ) * ((fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 0) +
            σ * ((fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 1) := by
          have h_eq : σ = (1 - σ) • (0 : ℝ) + σ • (1 : ℝ) := by simp [smul_eq_mul] <;> ring
          rw [h_eq]
          have h := h21.2 h0_in h1_in h_a_nonneg h_b_nonneg h_sum_one
          simpa [smul_eq_mul] using h
        rw [h22, h23] at h_main
        simpa using h_main
      exact h2 σ ⟨by linarith, by linarith⟩
    have h4 : Real.exp (σ * t) - 1 ≤ σ * (Real.exp t - 1) := by linarith
    have h5 : (Real.exp (σ * t) - 1) / σ ≤ Real.exp t - 1 := by
      calc
        (Real.exp (σ * t) - 1) / σ ≤ (σ * (Real.exp t - 1)) / σ := by gcongr
        _ = Real.exp t - 1 := by
          field_simp [hσ_pos.ne'] <;> ring
    have h6 : Real.exp t - 1 ≤ t := h
    have h7 : (Real.exp (σ * t) - 1) / σ ≤ t := by linarith
    have h8 : t = Real.log X := by rw [ht_def]
    rw [h8] at h7
    exact le_trans h7 (le_max_of_le_left (le_refl (Real.log X)))
  · -- 情况 2：t < Real.exp t - 1
    -- 我们需要证明 (Real.exp (σ * t) - 1) / σ ≤ Real.exp t - 1
    -- 令 g(σ) = Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)
    -- 我们需要证明 g(σ) ≤ 0
    have h21 : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) := by
      -- 先在整个实数域上证明凸性，再限制到 Set.Icc 0 1
      have h_g_convex_univ : ConvexOn ℝ Set.univ
          (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) := by
        -- 1. 证明 fun σ => Real.exp (σ * t) 凸
        have h1 : ConvexOn ℝ Set.univ (fun σ : ℝ => Real.exp (σ * t)) :=
          test_exp_linear_convex t
        -- 2. 证明 fun σ => σ * (-(Real.exp t - 1)) 凸
        have h2 : ConvexOn ℝ Set.univ (fun σ : ℝ => σ * (-(Real.exp t - 1))) :=
          test_linear_convex (-(Real.exp t - 1))
        -- 3. 常数函数 -1 凸
        have h3 : ConvexOn ℝ Set.univ (fun _ : ℝ => (-1 : ℝ)) :=
          convexOn_const (-1) convex_univ
        -- 4. 合并：h1 + h2 + h3
        have h_sum : ConvexOn ℝ Set.univ
            (fun σ : ℝ => Real.exp (σ * t) + σ * (-(Real.exp t - 1)) + (-1)) :=
          (h1.add h2).add h3
        -- 5. 转换成目标函数形式
        convert h_sum using 1
        ext σ
        ring
      -- 限制到子集 Set.Icc 0 1
      have h_convex_Icc : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
      have h_subset : (Set.Icc (0:ℝ) 1) ⊆ Set.univ := by
        exact Set.subset_univ (Set.Icc (0:ℝ) 1)
      exact h_g_convex_univ.subset h_subset h_convex_Icc
    have h22 : (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 0 = 0 := by
      simp
      <;> ring
    have h23 : (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 1 = 0 := by
      simp
      <;> ring
    have h2 : ∀ σ ∈ Set.Icc (0 : ℝ) 1, Real.exp (σ * t) - 1 - σ * (Real.exp t - 1) ≤ 0 := by
      intro σ hσ
      have h_a_nonneg : 0 ≤ 1 - σ := by exact sub_nonneg.mpr hσ.2
      have h_b_nonneg : 0 ≤ σ := by exact hσ.1
      have h_sum_one : (1 - σ) + σ = 1 := by ring
      have h0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.mem_Icc]
      have h1_in : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.mem_Icc]
      have h_main : (fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) σ ≤
          (1 - σ) * ((fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 0) +
          σ * ((fun σ : ℝ => Real.exp (σ * t) - 1 - σ * (Real.exp t - 1)) 1) := by
        have h_eq : σ = (1 - σ) • (0 : ℝ) + σ • (1 : ℝ) := by simp [smul_eq_mul] <;> ring
        rw [h_eq]
        have h := h21.2 h0_in h1_in h_a_nonneg h_b_nonneg h_sum_one
        simpa [smul_eq_mul] using h
      rw [h22, h23] at h_main
      simpa using h_main
    have h3 : Real.exp (σ * t) - 1 - σ * (Real.exp t - 1) ≤ 0 := h2 σ ⟨by linarith, by linarith⟩
    have h4 : Real.exp (σ * t) - 1 ≤ σ * (Real.exp t - 1) := by linarith
    have h5 : (Real.exp (σ * t) - 1) / σ ≤ Real.exp t - 1 := by
      calc
        (Real.exp (σ * t) - 1) / σ ≤ (σ * (Real.exp t - 1)) / σ := by gcongr
        _ = Real.exp t - 1 := by
          field_simp [hσ_pos.ne'] <;> ring
    have h6 : Real.exp t - 1 = X - 1 := by
      rw [hX_eq] <;> ring
    rw [h6] at h5
    exact le_trans h5 (le_max_of_le_right (le_refl (X - 1)))
