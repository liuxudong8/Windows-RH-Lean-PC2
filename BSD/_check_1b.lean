import BSD.LSeries5
import Mathlib.Analysis.Complex.Basic

noncomputable section
open BigOperators

namespace BSD.LSeries5

/- ①b 阶段 1 探针 v2：ppow 素幂递推 + Satake 幂和桥 + 素幂界 -/

/-- 素幂 Hecke 系数：a₀ = 1, a₁ = a, a_{k+1} = a·a_k − p·a_{k-1}。 -/
def ppow (a : ℤ) (p : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => a
  | k + 2 => a * ppow a p (k + 1) - p * ppow a p k

lemma ppow_0 (a : ℤ) (p : ℕ) : ppow a p 0 = 1 := rfl
lemma ppow_1 (a : ℤ) (p : ℕ) : ppow a p 1 = a := rfl
lemma ppow_rec (a : ℤ) (p : ℕ) (k : ℕ) :
    ppow a p (k + 2) = a * ppow a p (k + 1) - p * ppow a p k := rfl

/-- 好素口径的 a_p(E⁵)：5 处加性（a=0）、37 处乘性（a=+1）、好素 χ₅(p)·a_p(E)。 -/
def ap5_prime_coeff (p : ℕ) : ℤ :=
  if p % 5 = 0 then 0 else if p = 37 then 1 else chi5 p * ap_E p

/-- Deligne（Weil 猜想）对 E⁵：好素 p 处 Satake 参数 α_p, β_p 存在，
    α_p + β_p = a_p(E⁵)，α_p β_p = p，‖α_p‖ = ‖β_p‖ = √p。
    升级路径：Deligne 定理（与 ramanujan_ap_E 同级，永久 axiom 风险）。
    注：由 ‖α‖ = ‖β‖ = √p 可推出 |a_p| ≤ 2√p（三角不等式），素幂界即由此出。 -/
axiom ap5_satake (p : ℕ) (hp : Nat.Prime p) :
    ∃ α β : ℂ, (α + β : ℂ) = (ap5_prime_coeff p : ℂ) ∧ α * β = (p : ℂ) ∧
      ‖α‖ = Real.sqrt (p : ℝ) ∧ ‖β‖ = Real.sqrt (p : ℝ)

/-- 幂和 s_k = Σ_{j=0}^{k} α^(k−j) β^j。 -/
def ssum (α β : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), α ^ (k - j) * β ^ j

/-- α·(α^m·β^n) = α^(m+1)·β^n。 -/
lemma pow_mul_pow_aux' (α β : ℂ) (m n : ℕ) :
    α * (α ^ m * β ^ n) = α ^ (m + 1) * β ^ n := by
  rw [pow_succ]
  ring

/-- β·(α^m·β^n) = α^m·β^(n+1)。 -/
lemma pow_mul_pow_aux'' (α β : ℂ) (m n : ℕ) :
    β * (α ^ m * β ^ n) = α ^ m * β ^ (n + 1) := by
  rw [pow_succ]
  ring

/-- (α·β)·(α^m·β^n) = α^(m+1)·β^(n+1)。 -/
lemma pow_mul_pow_aux (α β : ℂ) (m n : ℕ) :
    (α * β) * (α ^ m * β ^ n) = α ^ (m + 1) * β ^ (n + 1) := by
  rw [pow_succ, pow_succ]
  ring

/-- 第一项展开：α·(α^(k+1−j)β^j) 求和 = α^(k+2−j)β^j 求和 + α·β^(k+1)。 -/
lemma sumA (α β : ℂ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 2), α * (α ^ (k + 1 - j) * β ^ j))
      = (∑ j ∈ Finset.range (k + 1), α ^ (k + 2 - j) * β ^ j) + α * β ^ (k + 1) := by
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ k := by
      have hlt : j < k + 1 := Finset.mem_range.mp hj
      omega
    rw [show k + 2 - j = (k + 1 - j) + 1 by omega]
    exact pow_mul_pow_aux' α β (k + 1 - j) j
  · simp

/-- 第二项展开：β·(α^(k+1−j)β^j) 求和 = α^(k+1−j)β^(j+1) 求和 + β^(k+2)。 -/
lemma sumB (α β : ℂ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 2), β * (α ^ (k + 1 - j) * β ^ j))
      = (∑ j ∈ Finset.range (k + 1), α ^ (k + 1 - j) * β ^ (j + 1)) + β ^ (k + 2) := by
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ k := by
      have hlt : j < k + 1 := Finset.mem_range.mp hj
      omega
    exact pow_mul_pow_aux'' α β (k + 1 - j) j
  · rw [pow_mul_pow_aux'']
    rw [show k + 1 - (k + 1) = 0 by omega]
    rw [pow_zero, one_mul]

/-- 第三项：(αβ)·(α^(k−j)β^j) 求和 = α^(k+1−j)β^(j+1) 求和。 -/
lemma sumC (α β : ℂ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (α * β) * (α ^ (k - j) * β ^ j))
      = ∑ j ∈ Finset.range (k + 1), α ^ (k + 1 - j) * β ^ (j + 1) := by
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := by
    have hlt : j < k + 1 := Finset.mem_range.mp hj
    omega
  rw [show k + 1 - j = (k - j) + 1 by omega]
  exact pow_mul_pow_aux α β (k - j) j

/-- 左端展开：α^(k+2−j)β^j 求和 = (j=0..k 部分) + αβ^(k+1) + β^(k+2)。 -/
lemma sumL (α β : ℂ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 3), α ^ (k + 2 - j) * β ^ j)
      = (∑ j ∈ Finset.range (k + 1), α ^ (k + 2 - j) * β ^ j) + α * β ^ (k + 1) + β ^ (k + 2) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp

/-- 幂和满足 Hecke 递推（Newton 恒等式）：s_{k+2} = (α+β)s_{k+1} − αβ s_k。 -/
lemma ssum_rec (α β : ℂ) (k : ℕ) :
    ssum α β (k + 2) = (α + β) * ssum α β (k + 1) - α * β * ssum α β k := by
  unfold ssum
  rw [add_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [sumA, sumB, sumC, sumL]
  ring

/-- 幂和桥：ppow 的复值等于幂和（归纳）。 -/
lemma ppow_eq_ssum (a : ℤ) (p : ℕ) (α β : ℂ) (hsum : (α + β : ℂ) = (a : ℂ))
    (hprod : α * β = (p : ℂ)) : ∀ k : ℕ, (ppow a p k : ℂ) = ssum α β k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp [ppow, ssum]
  | one =>
      unfold ssum
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simpa [hsum] using (ppow_1 a p : ppow a p 1 = a)
  | more k ih1 ih2 =>
      calc
        (ppow a p (k + 2) : ℂ) = (a : ℂ) * (ppow a p (k + 1) : ℂ) - (p : ℂ) * (ppow a p k : ℂ) := by
          rw [ppow_rec]
          norm_num
        _ = (α + β) * ssum α β (k + 1) - α * β * ssum α β k := by
          rw [hsum, hprod, ih1, ih2]
        _ = ssum α β (k + 2) := (ssum_rec α β k).symm

/-- 幂和的上界：‖s_k‖ ≤ (k+1)(√p)^k，当 ‖α‖ = ‖β‖ = √p。 -/
lemma ssum_abs_bound (α β : ℂ) {p : ℕ} (hα : ‖α‖ = Real.sqrt (p : ℝ))
    (hβ : ‖β‖ = Real.sqrt (p : ℝ)) (k : ℕ) :
    ‖ssum α β k‖ ≤ (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k := by
  unfold ssum
  calc
    ‖∑ j ∈ Finset.range (k + 1), α ^ (k - j) * β ^ j‖ ≤
        (∑ j ∈ Finset.range (k + 1), ‖α ^ (k - j) * β ^ j‖) := norm_sum_le _ _
    _ ≤ (∑ j ∈ Finset.range (k + 1), (Real.sqrt (p : ℝ)) ^ (k - j) * (Real.sqrt (p : ℝ)) ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ k := by
        have hlt : j < k + 1 := Finset.mem_range.mp hj
        omega
      rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_pow, hα, hβ]
    _ = (∑ _ ∈ Finset.range (k + 1), (Real.sqrt (p : ℝ)) ^ k) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ k := by
        have hlt : j < k + 1 := Finset.mem_range.mp hj
        omega
      rw [← pow_add]
      congr 1
      omega
    _ = (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k := by
      rw [Finset.sum_const, Finset.card_range]
      ring

/-- 素幂界：|a_{p^k}(E⁵)| ≤ (k+1)p^{k/2}（对素 p；p^{k/2} 记为 (√p)^k）。 -/
theorem ppow_bound {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    (((|ppow (ap5_prime_coeff p) p k| : ℤ) : ℝ) ≤ (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k) := by
  obtain ⟨α, β, hsum, hprod, hα, hβ⟩ := ap5_satake p hp
  have hbridge : (ppow (ap5_prime_coeff p) p k : ℂ) = ssum α β k :=
    ppow_eq_ssum (ap5_prime_coeff p) p α β hsum hprod k
  have hcast : ‖((ppow (ap5_prime_coeff p) p k : ℤ) : ℂ)‖ =
      ((|ppow (ap5_prime_coeff p) p k| : ℤ) : ℝ) := by
    rw [Complex.norm_intCast]
    rw [Int.cast_abs]
  calc
    ((|ppow (ap5_prime_coeff p) p k| : ℤ) : ℝ) = ‖((ppow (ap5_prime_coeff p) p k : ℤ) : ℂ)‖ := by
      rw [hcast]
    _ = ‖ssum α β k‖ := by rw [hbridge]
    _ ≤ (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k := ssum_abs_bound α β hα hβ k

end BSD.LSeries5
