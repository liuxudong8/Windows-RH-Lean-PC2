import BSD._check_1b

noncomputable section
open BigOperators

namespace BSD.LSeries5

/- ①b 阶段 2 探针：乘性组装（素幂界 → τ(n)√n 全 n 界） -/

/-- ℝ 有限乘积逐项比较（非负版）。 -/
lemma prod_le_prod_nonneg {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hg0 : ∀ i ∈ s, 0 ≤ g i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    (∏ i ∈ s, f i) ≤ ∏ i ∈ s, g i := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (by simp))
      (ih (by intro i hi; exact hf0 i (by simp [hi]))
          (by intro i hi; exact hg0 i (by simp [hi]))
          (by intro i hi; exact hfg i (by simp [hi])))
      (Finset.prod_nonneg (by intro i hi; exact hf0 i (by simp [hi])))
      (hg0 a (by simp))

/-- ℤ 绝对值的乘积：|∏ z_i| = ∏ |z_i|。 -/
lemma abs_prod_int {ι : Type*} (s : Finset ι) (z : ι → ℤ) :
    |∏ i ∈ s, z i| = ∏ i ∈ s, |z i| := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.abs_mul, ih]

/-- 幂的平方根：√(p)^k = √(p^k)，p ≥ 0。 -/
lemma sqrt_pow_eq (p k : ℕ) : (Real.sqrt (p : ℝ)) ^ k = Real.sqrt ((p : ℝ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih]
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ k) (by positivity : (0 : ℝ) ≤ (p : ℝ))]
      congr 1
      rw [pow_succ', mul_comm]

/-- 乘积的平方根：∏ √(x_i) = √(∏ x_i)，x_i ≥ 0（本例 x_i = p^{k_p} ≥ 0）。 -/
lemma sqrt_prod_eq (n : ℕ) :
    (∏ p ∈ n.primeFactors, Real.sqrt ((p : ℝ) ^ n.factorization p))
      = Real.sqrt (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) := by
  classical
  induction' n.primeFactors using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.prod_insert ha, Finset.prod_insert ha, ih]
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a : ℝ) ^ n.factorization a)
        (by positivity : (0 : ℝ) ≤ ∏ p ∈ s, (p : ℝ) ^ n.factorization p)]

/-- 素因子分解：n = ∏_{p ∈ primeFactors n} p^{k_p}（ℝ 口径）。 -/
lemma prod_primeFactors_pow_eq (n : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
  norm_cast
  exact Nat.prod_factorization_pow_eq_self hn

/-- 乘性组装：素因子分解下的 Π a_{p^{k_p}} 满足 τ(n)√n 界。
    数学内容 = ①b 素幂界（ppow_bound）的乘性组合：|a_n| ≤ Π (k_p+1)(√p)^{k_p} = τ(n)√n。
    注：ppow(ap5 p, p, k) 是 a_{p^k} 的 Hecke 递推值；对好素 p 与真实系数一致，
    对坏素（5、37）该界作为代数界仍成立（真实 a_{5^k}=0、a_{37^k}=1 更紧）。 -/
theorem coefficient_bound_assembled (n : ℕ) (hn : n ≠ 0) :
    (|∏ p ∈ n.primeFactors, ppow (ap5_prime_coeff p) p (n.factorization p)| : ℝ)
      ≤ (Nat.divisors n).card * Real.sqrt (n : ℝ) := by
  have hsqrt_pow : ∀ p k : ℕ, (Real.sqrt (p : ℝ)) ^ k = Real.sqrt ((p : ℝ) ^ k) := sqrt_pow_eq
  have hsqrt_prod : (∏ p ∈ n.primeFactors, Real.sqrt ((p : ℝ) ^ n.factorization p))
      = Real.sqrt (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) := sqrt_prod_eq n
  have hprod_n : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) :=
    prod_primeFactors_pow_eq n hn
  have hsqrt : (∏ p ∈ n.primeFactors, (Real.sqrt (p : ℝ)) ^ n.factorization p) = Real.sqrt (n : ℝ) := by
    calc
      (∏ p ∈ n.primeFactors, (Real.sqrt (p : ℝ)) ^ n.factorization p)
          = ∏ p ∈ n.primeFactors, Real.sqrt ((p : ℝ) ^ n.factorization p) := by
              apply Finset.prod_congr rfl
              intro p hp
              exact hsqrt_pow p (n.factorization p)
      _ = Real.sqrt (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) := hsqrt_prod
      _ = Real.sqrt (n : ℝ) := by rw [hprod_n]
  have htau : (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)) = (Nat.divisors n).card := by
    norm_cast
    exact Nat.card_divisors hn
  calc
    (|∏ p ∈ n.primeFactors, ppow (ap5_prime_coeff p) p (n.factorization p)| : ℝ)
        = (∏ p ∈ n.primeFactors, (|ppow (ap5_prime_coeff p) p (n.factorization p)| : ℝ)) := by
          norm_cast
          exact abs_prod_int n.primeFactors (fun p => ppow (ap5_prime_coeff p) p (n.factorization p))
    _ ≤ (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) * (Real.sqrt (p : ℝ)) ^ n.factorization p) := by
          apply prod_le_prod_nonneg
          · intro p hp
            exact abs_nonneg _
          · intro p hp
            exact mul_nonneg (by positivity) (pow_nonneg (Real.sqrt_nonneg _) _)
          · intro p hp
            exact ppow_bound ((Nat.mem_primeFactors.mp hp).1) (n.factorization p)
    _ = (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)) *
        (∏ p ∈ n.primeFactors, (Real.sqrt (p : ℝ)) ^ n.factorization p) := by
          rw [Finset.prod_mul_distrib]
    _ = (Nat.divisors n).card * Real.sqrt (n : ℝ) := by
          rw [htau, hsqrt]

end BSD.LSeries5
