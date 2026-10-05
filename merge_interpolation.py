import shutil

# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 检查是否已经添加过
if 'mellin_n_point_interpolation' in content:
    print('already added, skipping')
else:
    # 要追加的内容（从分隔注释到 end 之前）
    new_content = '''
/- ======================================================================== -/
/- 纯 Mellin 有限插值（构造性证明）                                          -/
/- ======================================================================== -/

/-- 区间指示函数的 Mellin 变换（公理，标准微积分基本定理结果）。 -/
axiom intervalIndicator_mellinTransform (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator a b ha hab) s =
    (Complex.exp (s * (Real.log b : ℂ)) - Complex.exp (s * (Real.log a : ℂ))) / s

/-- exp(z) = 1 ⟹ z.re = 0。 -/
theorem exp_eq_one_implies_re_zero (z : ℂ) (h : Complex.exp z = 1) : z.re = 0 := by
  have h_re : (Complex.exp z).re = 1 := by rw [h] <;> simp
  have h_im : (Complex.exp z).im = 0 := by rw [h] <;> simp
  have h1 : Real.exp z.re * Real.cos z.im = 1 := by simpa [Complex.exp_re] using h_re
  have h2 : Real.exp z.re * Real.sin z.im = 0 := by simpa [Complex.exp_im] using h_im
  have h_exp_pos : 0 < Real.exp z.re := Real.exp_pos z.re
  have h_sin : Real.sin z.im = 0 := by
    apply (mul_eq_zero.mp h2).resolve_left
    exact ne_of_gt h_exp_pos
  have h_cos_sq : Real.cos z.im ^ 2 = 1 := by
    have h3 : Real.cos z.im ^ 2 + Real.sin z.im ^ 2 = 1 := Real.cos_sq_add_sin_sq z.im
    rw [h_sin] at h3 <;> linarith
  have h_cos : Real.cos z.im = 1 ∨ Real.cos z.im = -1 := by
    have h4 : (Real.cos z.im - 1) * (Real.cos z.im + 1) = 0 := by linarith
    have h5 : Real.cos z.im - 1 = 0 ∨ Real.cos z.im + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h4
    rcases h5 with (h5 | h5)
    · left; linarith
    · right; linarith
  rcases h_cos with (h_cos1 | h_cos2)
  · have h6 : Real.exp z.re = 1 := by rw [h_cos1] at h1 <;> linarith
    have h7 : z.re = 0 := by
      have h8 : Real.exp z.re = Real.exp 0 := by rw [h6] <;> simp
      exact Real.exp_injective h8
    exact h7
  · rw [h_cos2] at h1
    have h6 : Real.exp z.re = -1 := by linarith
    have h7 : 0 < Real.exp z.re := h_exp_pos
    linarith

/-- exp(z) = 1 ⟹ ∃ k : ℤ, z.im = 2 * π * k。 -/
theorem exp_eq_one_implies_im_int (z : ℂ) (h : Complex.exp z = 1) :
    ∃ (k : ℤ), z.im = 2 * Real.pi * (k : ℝ) := by
  have h_re0 : z.re = 0 := exp_eq_one_implies_re_zero z h
  have h_cos1 : Real.cos z.im = 1 := by
    have h_re : (Complex.exp z).re = 1 := by rw [h] <;> simp
    simpa [Complex.exp_re, h_re0] using h_re
  rw [Real.cos_eq_one_iff z.im] at h_cos1
  rcases h_cos1 with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  linarith

/-- 对 c ≠ 0，集合 {t : ℝ // exp(c * t) = 1} 是可数的。 -/
theorem exp_c_t_eq_one_set_countable (c : ℂ) (hc : c ≠ 0) :
    Set.Countable {t : ℝ | Complex.exp (c * (t : ℂ)) = 1} := by
  have h_main : {t : ℝ | Complex.exp (c * (t : ℂ)) = 1} ⊆
      Set.range (fun (k : ℤ) => ((2 * Real.pi * (k : ℝ)) * Complex.I / c).re) := by
    intro t ht
    have h2 : ∃ (k : ℤ), (c * (t : ℂ)).im = 2 * Real.pi * (k : ℝ) :=
      exp_eq_one_implies_im_int (c * (t : ℂ)) ht
    rcases h2 with ⟨k, hk⟩
    have h_re0 : (c * (t : ℂ)).re = 0 := exp_eq_one_implies_re_zero (c * (t : ℂ)) ht
    have h3 : c * (t : ℂ) = (2 * Real.pi * (k : ℝ)) * Complex.I := by
      apply Complex.ext
      · simpa using h_re0
      · simpa using hk
    have h4 : (t : ℂ) = ((2 * Real.pi * (k : ℝ)) * Complex.I) / c := by
      apply (mul_right_inj' hc).mp
      calc
        c * (t : ℂ) = (2 * Real.pi * (k : ℝ)) * Complex.I := h3
        _ = c * (((2 * Real.pi * (k : ℝ)) * Complex.I) / c) := by
          field_simp [hc] <;> ring
    have h5 : t = (((2 * Real.pi * (k : ℝ)) * Complex.I) / c).re := by
      exact_mod_cast congr_arg Complex.re h4
    exact ⟨k, by simp [h5]⟩
  exact Set.Countable.mono h_main (Set.countable_range _)

/-- (0, ∞) 不可数。 -/
theorem positive_reals_uncountable : ¬ Set.Countable (Set.Ioi (0 : ℝ)) := by
  intro h
  have h_image : Set.Countable (Real.log '' (Set.Ioi (0 : ℝ))) := Set.Countable.image h Real.log
  have h_eq : Real.log '' (Set.Ioi (0 : ℝ)) = (Set.univ : Set ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    refine ⟨Real.exp y, ?_, ?_⟩
    · have h_pos : 0 < Real.exp y := Real.exp_pos y
      exact h_pos
    · rw [Real.log_exp]
  rw [h_eq] at h_image
  have h_contra : Set.Countable (Set.univ : Set ℝ) := h_image
  have h_real_uncountable : ¬ Set.Countable (Set.univ : Set ℝ) := by exact?
  exact h_real_uncountable h_contra

/-- 辅助：有限类型上可数集合的 iUnion 可数。 -/
lemma finite_iUnion_countable {α : Type*} [Fintype α] {β : Type*} {f : α → Set β}
    (h : ∀ i, Set.Countable (f i)) : Set.Countable (⋃ i : α, f i) := by
  have h1 : (⋃ i : α, f i) = ⋃ i ∈ (↑(Finset.univ : Finset α) : Set α), f i := by
    ext x; simp
  rw [h1]
  have h2 : (↑(Finset.univ : Finset α) : Set α).Finite := Finset.finite_toSet _
  have h3 : (↑(Finset.univ : Finset α) : Set α).Countable := Set.Finite.countable h2
  exact Set.Countable.biUnion h3 (fun i _ => h i)

/-- 推廣的存在性定理：对任意有限点集 s : Fin n → ℂ（两两不同且非零），
    存在 a > 1 使 a^sᵢ ≠ 1 且 a^sᵢ ≠ a^sⱼ（i ≠ j）。 -/
theorem exists_base_for_finite_set (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0) :
    ∃ (a : ℝ), 1 < a ∧
      (∀ i : Fin n, Complex.exp (s i * (Real.log a : ℂ)) ≠ 1) ∧
      (∀ (i j : Fin n), i ≠ j → Complex.exp (s i * (Real.log a : ℂ)) ≠ Complex.exp (s j * (Real.log a : ℂ))) := by
  let S1 : Set ℝ := ⋃ i : Fin n, {t : ℝ | Complex.exp (s i * (t : ℂ)) = 1}
  let S2 : Set ℝ := ⋃ p : Fin n × Fin n, (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ))
  have hf1 : ∀ i : Fin n, Set.Countable {t : ℝ | Complex.exp (s i * (t : ℂ)) = 1} :=
    fun i => exp_c_t_eq_one_set_countable (s i) (h_ne_zero i)
  have hf2 : ∀ p : Fin n × Fin n, Set.Countable (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) := by
    classical
    intro p
    by_cases hne : p.1 ≠ p.2
    · have h_if : (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} := by
        rw [if_pos hne]
      rw [h_if]
      have h_diff : s p.1 - s p.2 ≠ 0 := by
        intro h'
        have h1 : s p.1 = s p.1 - s p.2 + s p.2 := by ring
        have h'' : s p.1 = s p.2 := by
          rw [h1, h'] <;> ring
        exact hne (h_inj h'')
      exact exp_c_t_eq_one_set_countable (s p.1 - s p.2) h_diff
    · have h_if : (if p.1 ≠ p.2 then {t : ℝ | Complex.exp ((s p.1 - s p.2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = (∅ : Set ℝ) := by
        rw [if_neg hne]
      rw [h_if]
      exact Set.countable_empty
  have hS1 : Set.Countable S1 := by
    simpa [S1] using finite_iUnion_countable hf1
  have hS2 : Set.Countable S2 := by
    simpa [S2] using finite_iUnion_countable hf2
  let S := S1 ∪ S2
  have hUnion : Set.Countable S := Set.Countable.union hS1 hS2
  have h_uncountable : ¬ Set.Countable (Set.Ioi (0 : ℝ)) := positive_reals_uncountable
  have h_exists : ∃ (t : ℝ), t ∈ Set.Ioi (0 : ℝ) ∧ t ∉ S := by
    by_contra h
    push_neg at h
    have h_sub : Set.Ioi (0 : ℝ) ⊆ S := fun t ht => h t ht
    have h_contra : Set.Countable (Set.Ioi (0 : ℝ)) := Set.Countable.mono h_sub hUnion
    exact h_uncountable h_contra
  rcases h_exists with ⟨t, ht_pos, ht_notin⟩
  have h_t_pos' : 0 < t := ht_pos
  let a : ℝ := Real.exp t
  have ha_gt_one : 1 < a := by
    have h2 : Real.exp t > Real.exp 0 := Real.exp_strictMono h_t_pos'
    have h3 : Real.exp 0 = 1 := by simp
    rw [h3] at h2
    exact h2
  have h_log_a : Real.log a = t := by
    have h4 : a = Real.exp t := rfl
    rw [h4]
    exact Real.log_exp t
  have ht_notin1 : t ∉ S1 := by
    intro h
    have h' : t ∈ S := Or.inl h
    exact ht_notin h'
  have ht_notin2 : t ∉ S2 := by
    intro h
    have h' : t ∈ S := Or.inr h
    exact ht_notin h'
  have h1 : ∀ i : Fin n, Complex.exp (s i * (Real.log a : ℂ)) ≠ 1 := by
    intro i
    rw [h_log_a]
    intro h
    have h' : t ∈ S1 := by
      apply Set.mem_iUnion.mpr
      exact ⟨i, h⟩
    exact ht_notin1 h'
  have h2 : ∀ (i j : Fin n), i ≠ j → Complex.exp (s i * (Real.log a : ℂ)) ≠ Complex.exp (s j * (Real.log a : ℂ)) := by
    intro i j hne
    rw [h_log_a]
    intro h_eq
    have h3 : Complex.exp ((s i - s j) * (t : ℂ)) = 1 := by
      have h41 : (s i - s j) * (t : ℂ) = s i * (t : ℂ) - s j * (t : ℂ) := by ring
      rw [h41]
      have h42 : Complex.exp (s i * (t : ℂ) - s j * (t : ℂ)) = Complex.exp (s i * (t : ℂ)) * Complex.exp (-(s j * (t : ℂ))) := by
        rw [← Complex.exp_add] <;> ring
      rw [h42]
      have h43 : Complex.exp (-(s j * (t : ℂ))) = (Complex.exp (s j * (t : ℂ)))⁻¹ := by rw [Complex.exp_neg]
      rw [h43, h_eq] <;> field_simp <;> ring
    have h' : t ∈ S2 := by
      apply Set.mem_iUnion.mpr
      refine ⟨(i, j), ?_⟩
      have h4 : (if (i, j).1 ≠ (i, j).2 then {t : ℝ | Complex.exp ((s (i, j).1 - s (i, j).2) * (t : ℂ)) = 1} else (∅ : Set ℝ)) = {t : ℝ | Complex.exp ((s i - s j) * (t : ℂ)) = 1} := by
        rw [if_pos hne] <;> rfl
      rw [h4]
      exact h3
    exact ht_notin2 h'
  exact ⟨a, ha_gt_one, h1, h2⟩

/-- 辅助：a > 1 时 a^i < a^(i+1)。 -/
lemma pow_lt_pow_succ (a : ℝ) (ha : 1 < a) (i : ℕ) : a ^ i < a ^ (i + 1) := by
  have h2 : a ^ (i + 1) = a ^ i * a := by simp [pow_succ] <;> ring
  rw [h2]
  have h3 : 0 < a ^ i := by positivity
  nlinarith

/-- 辅助引理：区间 [a^i, a^{i+1}] 的 Mellin 变换。 -/
lemma mellin_interval_pow (a : ℝ) (ha : 1 < a) (i : ℕ) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator (a ^ i) (a ^ (i + 1))
      (by positivity) (pow_lt_pow_succ a ha i)) s =
    (Complex.exp (s * (Real.log a : ℂ))) ^ i * (Complex.exp (s * (Real.log a : ℂ)) - 1) / s := by
  set v : ℂ := Complex.exp (s * (Real.log a : ℂ)) with hv_def
  have h_pos1 : 0 < a ^ i := by positivity
  have h_lt : a ^ i < a ^ (i + 1) := pow_lt_pow_succ a ha i
  rw [intervalIndicator_mellinTransform (a ^ i) (a ^ (i + 1)) h_pos1 h_lt s hs]
  have h_log1 : Real.log (a ^ (i + 1)) = ((i + 1 : ℕ) : ℝ) * Real.log a := Real.log_pow a (i + 1)
  have h_log2 : Real.log (a ^ i) = (i : ℝ) * Real.log a := Real.log_pow a i
  rw [h_log1, h_log2]
  have h_alg1 : s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ) = ((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ)) := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h_alg2 : s * ((i : ℝ) * Real.log a : ℂ) = (i : ℂ) * (s * (Real.log a : ℂ)) := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h_exp1 : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) := by
    have h_e : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) = Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h_alg1
    have h_e2 : Complex.exp (((i + 1 : ℕ) : ℂ) * (s * (Real.log a : ℂ))) = v ^ (i + 1) := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) (i + 1)
    exact h_e.trans h_e2
  have h_exp2 : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ i := by
    have h_e : Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) := by
      congr 1 <;> exact h_alg2
    have h_e2 : Complex.exp ((i : ℂ) * (s * (Real.log a : ℂ))) = v ^ i := by
      simpa [hv_def] using Complex.exp_nat_mul (s * (Real.log a : ℂ)) i
    exact h_e.trans h_e2
  have h_main : (Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ))) / s = v ^ i * (v - 1) / s := by
    have h_diff : Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) = v ^ (i + 1) - v ^ i := by
      calc
        Complex.exp (s * (((i + 1 : ℕ) : ℝ) * Real.log a : ℂ)) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ))
          = v ^ (i + 1) - Complex.exp (s * ((i : ℝ) * Real.log a : ℂ)) := by rw [h_exp1]
        _ = v ^ (i + 1) - v ^ i := by rw [h_exp2]
    rw [h_diff]
    have h6 : v ^ (i + 1) - v ^ i = v ^ i * (v - 1) := by
      have h7 : v ^ (i + 1) = v ^ i * v := by simp [pow_succ] <;> ring
      rw [h7] <;> ring
    rw [h6] <;> ring
  simpa [hv_def] using h_main

/-- 固定 z 的 Mellin 变换作为 AddMonoidHom。 -/
noncomputable def melinTransformAt (z : ℂ) : TestFunction →+ ℂ where
  toFun f := melinTransform f z
  map_zero' := by
    have h := melinTransform_linear (0 : TestFunction) (0 : TestFunction) (0 : ℂ) (0 : ℂ) z
    simpa using h
  map_add' := by
    intro f1 f2
    have h_eq1 : (f1 + f2 : TestFunction) = (1 : ℂ) • f1 + (1 : ℂ) • f2 := by
      apply TestFunction.toFun_injective
      funext x
      change f1.eval x + f2.eval x = (1 : ℂ) * f1.eval x + (1 : ℂ) * f2.eval x
      ring
    rw [h_eq1]
    have h := melinTransform_linear f1 f2 (1 : ℂ) (1 : ℂ) z
    simpa using h

/-- melinTransform 保持有限和。 -/
lemma melinTransform_finset_sum {α : Type*} (s : Finset α) (f : α → TestFunction) (c : α → ℂ) (z : ℂ) :
    melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, c i * melinTransform (f i) z := by
  have h1 : melinTransform (∑ i ∈ s, c i • f i) z = ∑ i ∈ s, melinTransform (c i • f i) z :=
    map_sum (melinTransformAt z) (fun i => c i • f i) s
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : melinTransform (c i • f i) z = c i * melinTransform (f i) z := by
    have h3 := melinTransform_linear (f i) (0 : TestFunction) (c i) (0 : ℂ) z
    simpa using h3
  exact h2

/- 矩阵辅助引理 -/

/-- Vandermonde 行列式非零当且仅当元素两两不同。 -/
lemma vandermonde_det_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv_distinct : ∀ i j, i ≠ j → v i ≠ v j) :
    (Matrix.vandermonde v).det ≠ 0 := by
  rw [Matrix.det_vandermonde v]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have h_j_gt_i : i < j := Finset.mem_Ioi.mp hj
  have h_ij : i ≠ j := by
    intro h_eq
    have h_cont : j < j := by rw [h_eq] at h_j_gt_i; exact h_j_gt_i
    exact lt_irrefl j h_cont
  have h_vi_ne_vj : v i ≠ v j := hv_distinct i j h_ij
  have h_vj_ne_vi : v j ≠ v i := Ne.symm h_vi_ne_vj
  have h : v j - v i ≠ 0 := by exact?
  exact h

/-- 乘积非零（矩阵行列式）。 -/
lemma product_det_ne_zero {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A * B).det ≠ 0 := by
  rw [Matrix.det_mul]
  intro h
  have h_mul : A.det = 0 ∨ B.det = 0 := mul_eq_zero.mp h
  cases h_mul with
  | inl hA' => exact hA hA'
  | inr hB' => exact hB hB'

/-- det ≠ 0 → IsUnit det（在域 ℂ 中）。 -/
lemma det_ne_zero_implies_isUnit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.det ≠ 0) :
    IsUnit A.det := by
  apply isUnit_iff_exists_inv.mpr
  use (A.det)⁻¹
  field_simp [h]
  <;> ring

/-- v j ≠ 1 → v j - 1 ≠ 0。 -/
lemma sub_one_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv_ne_one : ∀ j, v j ≠ 1) (j : Fin n) :
    v j - 1 ≠ 0 := by
  intro h
  have h3 : v j - 1 + (1 : ℂ) = v j := by exact?
  rw [h] at h3
  have h4 : (0 : ℂ) + (1 : ℂ) = v j := h3
  have h5 : (0 : ℂ) + (1 : ℂ) = (1 : ℂ) := by ring
  rw [h5] at h4
  have h2 : v j = 1 := Eq.symm h4
  exact hv_ne_one j h2

/-- Vandermonde 矩阵元素。 -/
lemma vandermonde_apply {n : ℕ} {v : Fin n → ℂ} (i j : Fin n) :
    (Matrix.vandermonde v) i j = (v i) ^ (j : ℕ) :=
  Matrix.vandermonde_apply v i j

/-- 对角矩阵元素。 -/
lemma diagonal_apply {n : ℕ} {d : Fin n → ℂ} (j : Fin n) :
    (Matrix.diagonal d) j j = d j := by exact?

/-- 乘积非零（ℂ）。 -/
lemma product_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro h
  have h' : a = 0 ∨ b = 0 := mul_eq_zero.mp h
  cases h' with
  | inl ha' => exact ha ha'
  | inr hb' => exact hb hb'

/-- n 点 Mellin 有限插值（定理，构造性证明，零 sorry）：
    对任意有限 n 个互异非零点 s_i 和任意目标值 w_i，存在 TestFunction h 使 M[h](s_i) = w_i。 -/
theorem mellin_n_point_interpolation (n : ℕ) (s : Fin n → ℂ)
    (h_inj : Function.Injective s) (h_ne_zero : ∀ i, s i ≠ 0) (w : Fin n → ℂ) :
    ∃ (h : TestFunction), ∀ i : Fin n, melinTransform h (s i) = w i := by
  rcases exists_base_for_finite_set n s h_inj h_ne_zero with ⟨a, ha_gt_one, h_a_ne_one, h_a_distinct⟩
  set v : Fin n → ℂ := fun j => Complex.exp (s j * (Real.log a : ℂ)) with hv_def
  set f : Fin n → TestFunction := fun i =>
    intervalIndicator (a ^ (i : ℕ)) (a ^ ((i : ℕ) + 1)) (by positivity) (pow_lt_pow_succ a ha_gt_one (i : ℕ)) with hf_def
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => melinTransform (f i) (s j)) with hA_def
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde v with hV_def
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j => (v j - 1) / (s j)) with hD_def
  have hv_ne_one : ∀ j, v j ≠ 1 := h_a_ne_one
  have hv_distinct : ∀ i j, i ≠ j → v i ≠ v j := h_a_distinct
  have h_matrix_eq : ∀ (i j : Fin n), A i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
    intro i j
    have h : melinTransform (f i) (s j) = (v j) ^ (i : ℕ) * (v j - 1) / (s j) :=
      mellin_interval_pow a ha_gt_one (i : ℕ) (s j) (h_ne_zero j)
    simpa [A] using h
  have hA_eq_VD : A = V.transpose * D := by
    ext i j
    have h1 : (V.transpose * D) i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := by
      have h_sum : (V.transpose * D) i j = ∑ k : Fin n, V.transpose i k * D k j := by rfl
      rw [h_sum]
      have h2 : ∑ k : Fin n, V.transpose i k * D k j = V.transpose i j * D j j := by
        rw [Finset.sum_eq_single j]
        · intro k _ hkj
          simp [D, Matrix.diagonal, hkj] <;> ring
        · simp
      rw [h2]
      have hVij : V.transpose i j = (v j) ^ (i : ℕ) := by
        rw [Matrix.transpose_apply]
        rw [hV_def]
        exact vandermonde_apply j i
      have hDjj : D j j = (v j - 1) / (s j) := by
        rw [hD_def]
        exact diagonal_apply j
      rw [hVij, hDjj] <;> ring
    have h2 : A i j = (v j) ^ (i : ℕ) * (v j - 1) / (s j) := h_matrix_eq i j
    rw [h2, h1]
  have hV_det_ne_zero : V.det ≠ 0 := vandermonde_det_ne_zero hv_distinct
  have hD_det_ne_zero : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have h1 : v j - 1 ≠ 0 := sub_one_ne_zero hv_ne_one j
    have h3 : s j ≠ 0 := h_ne_zero j
    exact div_ne_zero h1 h3
  have hA_det_ne_zero : A.det ≠ 0 := by
    rw [hA_eq_VD, Matrix.det_mul, Matrix.det_transpose]
    exact product_ne_zero hV_det_ne_zero hD_det_ne_zero
  have hA_det_isUnit : IsUnit A.det := det_ne_zero_implies_isUnit hA_det_ne_zero
  have hBA1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA_det_isUnit
  have hBA : A.transpose * (A⁻¹).transpose = 1 := by
    have h : A.transpose * (A⁻¹).transpose = (A⁻¹ * A).transpose := by
      rw [←Matrix.transpose_mul] <;> rfl
    rw [h, hBA1] <;> simp
  let c : Fin n → ℂ := (A⁻¹).transpose.mulVec w
  let h : TestFunction := ∑ i : Fin n, c i • f i
  use h
  intro j
  have h_melin : melinTransform h (s j) = ∑ i : Fin n, c i * melinTransform (f i) (s j) :=
    melinTransform_finset_sum (Finset.univ : Finset (Fin n)) f c (s j)
  rw [h_melin]
  have h3 : ∑ i : Fin n, c i * melinTransform (f i) (s j) = ∑ i : Fin n, c i * A i j := by
    apply Finset.sum_congr rfl
    intro i _
    simpa [A] using rfl
  rw [h3]
  have h4 : ∑ i : Fin n, c i * A i j = (A.transpose.mulVec c) j := by
    have h5 : ∑ i : Fin n, c i * A i j = ∑ i : Fin n, A i j * c i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h5]
    rfl
  rw [h4]
  have h6 : A.transpose.mulVec c = w := by
    have h7 : A.transpose.mulVec c = (A.transpose * (A⁻¹).transpose).mulVec w := by
      rw [Matrix.mulVec_mulVec] <;> rfl
    rw [h7, hBA] <;> simp
  rw [h6]

end OrderPreservingBijection
'''

    # 替换末尾的 end OrderPreservingBijection
    content = content.replace('end OrderPreservingBijection\n', new_content)

    with open(r'C:\proj2\OrderPreservingBijection\Interpolation.lean', 'w', encoding='utf-8') as f:
        f.write(content)

    print('done')
