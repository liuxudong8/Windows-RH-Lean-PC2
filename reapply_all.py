import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

# 1. Triangle inequality 4689
c = c.replace(
    "_ ≤ 1/(‖s‖ * ‖s + 1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by admit",
    "_ ≤ 1/(‖s‖ * ‖s + 1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by exact?"
)

# 2. h83 - replace admit with proper proof
old_h83 = "    have h83 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by admit"
new_h83 = """    have h831 : ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) = ∫ x in ε₀..R₀, x^(s.re + 1) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hε₀_lt_R₀.le]
    have h832 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) := by
      simp [integral_const_mul]
    have h833 : -1 < s.re + 1 := by linarith [hs_re1]
    have h834 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
      rw [integral_rpow (Or.inl h833)] <;> ring
    have h83 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
      rw [h832, h831, h834] <;> ring"""
assert old_h83 in c, "h83 not found"
c = c.replace(old_h83, new_h83)

# 3. h_s_im_ne_zero - add parameter to theorem statements
# mellin_rapid_decay_bound
c = c.replace(
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by\n  intro s hs_re1 hs_re2",
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (R₀ ^ 3 + 1) / |s.im| ^ 2 := by\n  intro s hs_re1 hs_re2 hs_im_ne_zero"
)
c = c.replace(
    "    have h_s_im_ne_zero : s.im ≠ 0 := by\n      admit",
    "    have h_s_im_ne_zero : s.im ≠ 0 := hs_im_ne_zero"
)

# mellin_transform_C2_rapid_decay
c = c.replace(
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 := by",
    "    ∀ (s : ℂ), 0 < s.re → s.re < 1 → s.im ≠ 0 →\n      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 := by"
)

# call site inside mellin_transform_C2_rapid_decay
c = c.replace(
    "  exact mellin_rapid_decay_bound h B' hC2 hB hB_pos ε₀ R₀ hε₀_pos hε₀_lt_R₀ h_h_left h_h_right h_u_eps0_zero h_u_R0_zero h_u'_eps0_zero h_u'_R0_zero",
    "  exact mellin_rapid_decay_bound h B' hC2 hB hB_pos ε₀ R₀ hε₀_pos hε₀_lt_R₀ h_h_left h_h_right h_u_eps0_zero h_u_R0_zero h_u'_eps0_zero h_u'_R0_zero s hs_re1 hs_re2 hs_im_ne_zero"
)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
