f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 修改 nontrivialZeroSum_pair_localization
old_pair = """/-- 非平凡零点求和的成对局部化（定理，由 tsum 线性性+两项隔离推出）：
    如果两个测试函数的 Mellin 变换在除 {ρ,1-ρ} 之外的所有非平凡零点处取值相同，
    则它们的 nontrivialZeroSum 之差完全由 {ρ,1-ρ} 处的 Mellin 变换之差决定。

    证明：
    (1) nontrivialZeroEnum_covers_all 给出 n₁, n₂ 使得 enum n₁=ρ, enum n₂=1-ρ
    (2) nontrivialZeroEnum_injective 给出 n₁ ≠ n₂
    (3) 对 n ≠ n₁, n₂，enum n ∉ {ρ,1-ρ}，故 M[f₁](enum n) = M[f₂](enum n)
    (4) 由 nontrivialZeroSum_tsum_linear + tsum_two_point_isolation，差 = 两项之和 -/
theorem nontrivialZeroSum_pair_localization (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ≠ 1 - ρ →
    ∀ (f1 f2 : TestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform f1 ρ' = melinTransform f2 ρ') →
      nontrivialZeroSum f1 - nontrivialZeroSum f2 =
        (melinTransform f1 ρ - melinTransform f2 ρ) +
        (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ)) := by
  intro hz hre1 hre2 h_ne_rho f1 f2 h_other
  rcases nontrivialZeroEnum_covers_all ρ hz hre1 hre2 with ⟨n1, hn1⟩
  have h_sym : _root_.riemannZeta (1 - ρ) = 0 ∧ 0 < (1 - ρ).re ∧ (1 - ρ).re < 1 :=
    riemann_zeta_zero_symmetry ρ hz hre1 hre2
  rcases nontrivialZeroEnum_covers_all (1 - ρ) h_sym.1 h_sym.2.1 h_sym.2.2 with ⟨n2, hn2⟩
  have h_n1_ne_n2 : n1 ≠ n2 := by
    intro h_eq
    have h : nontrivialZeroEnum n1 = nontrivialZeroEnum n2 := by rw [h_eq]
    rw [hn1, hn2] at h
    exact h_ne_rho h
  let a : ℕ → ℂ := fun n => melinTransform f1 (nontrivialZeroEnum n) - melinTransform f2 (nontrivialZeroEnum n)
  have h_vanish : ∀ (n : ℕ), n ≠ n1 → n ≠ n2 → a n = 0 := by
    intro n hne1 hne2
    have h_enum_ne_rho : nontrivialZeroEnum n ≠ ρ := by
      intro h
      have h' : n = n1 := nontrivialZeroEnum_injective (by rw [h, hn1])
      exact hne1 h'
    have h_enum_ne_1mr : nontrivialZeroEnum n ≠ 1 - ρ := by
      intro h
      have h' : n = n2 := nontrivialZeroEnum_injective (by rw [h, hn2])
      exact hne2 h'
    have hz' : _root_.riemannZeta (nontrivialZeroEnum n) = 0 := (nontrivialZeroEnum_are_zeros n).1
    have hre1' : 0 < (nontrivialZeroEnum n).re := (nontrivialZeroEnum_are_zeros n).2.1
    have hre2' : (nontrivialZeroEnum n).re < 1 := (nontrivialZeroEnum_are_zeros n).2.2
    have h_eq : melinTransform f1 (nontrivialZeroEnum n) = melinTransform f2 (nontrivialZeroEnum n) :=
      h_other (nontrivialZeroEnum n) hz' hre1' hre2' h_enum_ne_rho h_enum_ne_1mr
    simpa [a, sub_eq_zero] using h_eq
  have h_main : nontrivialZeroSum f1 - nontrivialZeroSum f2 = ∑' (n : ℕ), a n :=
    nontrivialZeroSum_tsum_linear f1 f2
  rw [h_main]
  have h_tsum : ∑' (n : ℕ), a n = a n1 + a n2 := tsum_two_point_isolation a n1 n2 h_n1_ne_n2 h_vanish
  rw [h_tsum]
  have h1 : a n1 = melinTransform f1 ρ - melinTransform f2 ρ := by simp [a, hn1]
  have h2 : a n2 = melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ) := by simp [a, hn2]
  rw [h1, h2]"""

new_pair = """/-- 非平凡零点求和的成对局部化（定理，带重数，由 tsum 线性性+两项隔离推出）：
    如果两个测试函数的 Mellin 变换在除 {ρ,1-ρ} 之外的所有非平凡零点处取值相同，
    则它们的 nontrivialZeroSum 之差完全由 {ρ,1-ρ} 处的 Mellin 变换之差决定，
    乘以零点重数 m(ρ)（由函数方程 m(ρ)=m(1-ρ)）。

    证明：
    (1) nontrivialZeroEnum_covers_all 给出 n₁, n₂ 使得 enum n₁=ρ, enum n₂=1-ρ
    (2) nontrivialZeroEnum_injective 给出 n₁ ≠ n₂
    (3) 对 n ≠ n₁, n₂，enum n ∉ {ρ,1-ρ}，故 M[f₁](enum n) = M[f₂](enum n)
    (4) 由 nontrivialZeroSum_tsum_linear + tsum_two_point_isolation，差 = m(ρ)*(两项之和) -/
theorem nontrivialZeroSum_pair_localization (ρ : ℂ) :
    _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ≠ 1 - ρ →
    ∀ (f1 f2 : TestFunction),
      (∀ (ρ' : ℂ), _root_.riemannZeta ρ' = 0 → 0 < ρ'.re → ρ'.re < 1 →
        ρ' ≠ ρ → ρ' ≠ 1 - ρ →
        melinTransform f1 ρ' = melinTransform f2 ρ') →
      nontrivialZeroSum f1 - nontrivialZeroSum f2 =
        (zeroMultiplicity ρ : ℂ) *
        ((melinTransform f1 ρ - melinTransform f2 ρ) +
         (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ))) := by
  intro hz hre1 hre2 h_ne_rho f1 f2 h_other
  rcases nontrivialZeroEnum_covers_all ρ hz hre1 hre2 with ⟨n1, hn1⟩
  have h_sym : _root_.riemannZeta (1 - ρ) = 0 ∧ 0 < (1 - ρ).re ∧ (1 - ρ).re < 1 :=
    riemann_zeta_zero_symmetry ρ hz hre1 hre2
  rcases nontrivialZeroEnum_covers_all (1 - ρ) h_sym.1 h_sym.2.1 h_sym.2.2 with ⟨n2, hn2⟩
  have h_n1_ne_n2 : n1 ≠ n2 := by
    intro h_eq
    have h : nontrivialZeroEnum n1 = nontrivialZeroEnum n2 := by rw [h_eq]
    rw [hn1, hn2] at h
    exact h_ne_rho h
  let a : ℕ → ℂ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℂ) *
    (melinTransform f1 (nontrivialZeroEnum n) - melinTransform f2 (nontrivialZeroEnum n))
  have h_vanish : ∀ (n : ℕ), n ≠ n1 → n ≠ n2 → a n = 0 := by
    intro n hne1 hne2
    have h_enum_ne_rho : nontrivialZeroEnum n ≠ ρ := by
      intro h
      have h' : n = n1 := nontrivialZeroEnum_injective (by rw [h, hn1])
      exact hne1 h'
    have h_enum_ne_1mr : nontrivialZeroEnum n ≠ 1 - ρ := by
      intro h
      have h' : n = n2 := nontrivialZeroEnum_injective (by rw [h, hn2])
      exact hne2 h'
    have hz' : _root_.riemannZeta (nontrivialZeroEnum n) = 0 := (nontrivialZeroEnum_are_zeros n).1
    have hre1' : 0 < (nontrivialZeroEnum n).re := (nontrivialZeroEnum_are_zeros n).2.1
    have hre2' : (nontrivialZeroEnum n).re < 1 := (nontrivialZeroEnum_are_zeros n).2.2
    have h_eq : melinTransform f1 (nontrivialZeroEnum n) = melinTransform f2 (nontrivialZeroEnum n) :=
      h_other (nontrivialZeroEnum n) hz' hre1' hre2' h_enum_ne_rho h_enum_ne_1mr
    simpa [a, h_eq, sub_eq_zero, mul_zero] using rfl
  have h_main : nontrivialZeroSum f1 - nontrivialZeroSum f2 = ∑' (n : ℕ), a n :=
    nontrivialZeroSum_tsum_linear f1 f2
  rw [h_main]
  have h_tsum : ∑' (n : ℕ), a n = a n1 + a n2 := tsum_two_point_isolation a n1 n2 h_n1_ne_n2 h_vanish
  rw [h_tsum]
  have h_m1 : (zeroMultiplicity (nontrivialZeroEnum n1) : ℂ) = (zeroMultiplicity ρ : ℂ) := by
    rw [hn1]
  have h_m2 : (zeroMultiplicity (nontrivialZeroEnum n2) : ℂ) = (zeroMultiplicity (1 - ρ) : ℂ) := by
    rw [hn2]
  have h_msym : (zeroMultiplicity (1 - ρ) : ℂ) = (zeroMultiplicity ρ : ℂ) := by
    exact_mod_cast zeroMultiplicity_symmetry ρ
  have h1 : a n1 = (zeroMultiplicity ρ : ℂ) * (melinTransform f1 ρ - melinTransform f2 ρ) := by
    simp [a, hn1, h_m1]
  have h2 : a n2 = (zeroMultiplicity ρ : ℂ) * (melinTransform f1 (1 - ρ) - melinTransform f2 (1 - ρ)) := by
    simp [a, hn2, h_m2, h_msym]
  rw [h1, h2]
  ring"""

content = content.replace(old_pair, new_pair, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Step 3 done: nontrivialZeroSum_pair_localization with multiplicity')
