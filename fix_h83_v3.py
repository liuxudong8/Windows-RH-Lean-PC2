import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = """    have h831 : ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) = ∫ x in ε₀..R₀, x^(s.re + 1) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hε₀_lt_R₀.le]
    have h832 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) := by
      rw [MeasureTheory.setIntegral_const_mul]
    have h833 : -1 < s.re + 1 := by linarith [hs_re1]
    have h834 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
      rw [intervalIntegral.integral_rpow (Or.inl h833)] <;> ring
    have h83 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
      rw [h832, h831, h834] <;> ring"""

new = """    have h831 : ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) = ∫ x in ε₀..R₀, x^(s.re + 1) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hε₀_lt_R₀.le]
    have h832 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) := by
      simp [integral_const_mul]
    have h833 : -1 < s.re + 1 := by linarith [hs_re1]
    have h834 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
      rw [integral_rpow (Or.inl h833)] <;> ring
    have h83 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
      rw [h832, h831, h834] <;> ring"""

assert old in c, "old not found"
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
