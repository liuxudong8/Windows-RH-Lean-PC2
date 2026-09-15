/-
  分层求和基础设施模块
  为 zero_weighted_series_summable 降级提供基础引理。
-/

import OrderPreservingBijection.stage_4

namespace SummabilityInfrastructure

open RHSpectralDuality

/-- 引理 1：从 encard 上界推出有限性。
    如果 Set.encard s ≤ (n : ENat)，则 s.Finite。 -/
lemma finite_of_encard_le {α : Type*} {s : Set α} {n : ℕ}
    (h : Set.encard s ≤ (n : ENat)) : s.Finite := by
  by_contra hinf
  have h_inf : s.Infinite := Set.not_finite.mp hinf
  have h_top : Set.encard s = ⊤ := Set.encard_eq_top h_inf
  rw [h_top] at h
  simp at h

/-- 引理 2：单射原像有限。
    如果 f 是单射且 f '' s 有限，则 s 有限。 -/
lemma finite_preimage_of_injective {α β : Type*} {f : α → β} {s : Set α}
    (h_inj : Function.Injective f) (h_fin : (f '' s).Finite) : s.Finite := by
  have h_inj_on : Set.InjOn f s := fun x _ y _ hxy => h_inj hxy
  have h : s = f ⁻¹' (f '' s) := by
    ext x
    simp [h_inj]
    <;> aesop
  rw [h]
  apply Set.Finite.preimage _ h_fin
  intro x _ y _ hxy
  exact h_inj hxy

/-- 引理 3：Set.Finite.toFinset 的成员关系。 -/
lemma toFinset_mem {α : Type*} {s : Set α} {hs : s.Finite} {x : α} :
    x ∈ (hs.toFinset) ↔ x ∈ s := by
  simp [Set.Finite.mem_toFinset]

/-- 引理 4：非负函数有限和一致有界判别法。
    如果 f : ℕ → ℝ 非负，且存在 M 使得对所有 n，∑_{i<n} f i ≤ M，
    则 Summable f。 -/
lemma summable_of_finite_bounded (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    (M : ℝ) (h_bound : ∀ (n : ℕ), ∑ i ∈ Finset.range n, f i ≤ M) : Summable f :=
  summable_of_sum_range_le hf_nonneg h_bound

/-- 引理 5：Real.log 的幂不等式。
    对 k : ℕ，log (2^k + 2) ≤ (k+2) * log 2。 -/
lemma log_pow_ineq (k : ℕ) : Real.log ((2^k : ℝ) + 2) ≤ ((k : ℝ) + 2) * Real.log 2 := by
  have h1 : (2^k : ℝ) + 2 ≤ (2^(k+2) : ℝ) := by
    have h21 : (1 : ℝ) ≤ (2^k : ℝ) := by
      have h211 : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
      exact_mod_cast h211
    have h22 : (2^k : ℝ) + 2 ≤ 4 * (2^k : ℝ) := by nlinarith
    have h23 : 4 * (2^k : ℝ) = (2^(k+2) : ℝ) := by
      simp [pow_succ] <;> ring
    rw [h23] at h22
    exact h22
  have h_pos : 0 < (2^k : ℝ) + 2 := by positivity
  have h2 : Real.log ((2^k : ℝ) + 2) ≤ Real.log (2^(k+2) : ℝ) :=
    Real.log_le_log h_pos h1
  rw [Real.log_pow] at h2
  <;> simpa using h2

end SummabilityInfrastructure
