# stage_4.lean Work Summary

## Project Overview

**Project**: Formalization of the Riemann Hypothesis (RH) in Lean 4, built on mathlib4 (v4.34.0-rc2).
**Main theorem**: `RHSpectralDuality.riemann_hypothesis` (stage_4.lean:5396)

## Work Completed This Session

### 1. `mellin_rapid_decay_bound` theorem fully closed

**Location**: stage_4.lean ~line 4349

**Previous state**: After restoring from backup `stage_4_before_h92_downgrade.lean`, there were 2 remaining admits:
- `h83`: ∫ B'·x^(σ+1) = B'(R₀^(σ+2)-ε₀^(σ+2))/(σ+2) (integral_rpow, set/interval bridge)
- `h_s_im_ne_zero`: s.im ≠ 0 (theorem statement gap)

**Completed fixes**:

#### a. Triangle inequality (~line 4689)
Directly reused the existing `h7` (proven at ~line 4475, bounding ‖1/(s(s+1)) · ∫ f‖).

#### b. h8 proof closure
```lean
rw [h83] at h82
exact mul_le_mul_of_nonneg_left h82 (by positivity)
```

#### c. h83 (Newton-Leibniz formula)
Key bridge lemma chain:
```lean
-- Icc → Ioc → interval integral
have h831 : ∫ x in Set.Icc ε₀ R₀, x^(s.re + 1) = ∫ x in ε₀..R₀, x^(s.re + 1) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hε₀_lt_R₀.le]
-- Factor out constant
have h832 : ∫ B' * x^r = B' * ∫ x^r := by simp [integral_const_mul]
-- Power function integral
have h834 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by
  rw [integral_rpow (Or.inl h833)] <;> ring
```

**Key lemma names**:
- `MeasureTheory.integral_Icc_eq_integral_Ioc`
- `intervalIntegral.integral_of_le h`
- `integral_const_mul`
- `integral_rpow (Or.inl h)` — note: global name, NOT `intervalIntegral.integral_rpow`

#### d. hs_im_ne_zero parameter added to theorem statements

Both theorems now take `(hs_im_ne_zero : s.im ≠ 0)`:

1. **`mellin_integral_bound_uniform`** (line 3030):
   - Statement: `0 < s.re → s.re < 1 → s.im ≠ 0 →`
   - Intro: `... hs_re1 hs_re2 hs_im_ne_zero`

2. **`mellin_pointwise_dual_norm_bound`** (line 3407):
   - Added parameter `(hs_im_ne_zero : s.im ≠ 0)`

3. **`mellin_constraint_dual_norm_uniform`** (line 3448), internal h2:
   - Statement added `s.im ≠ 0 →`
   - All call sites pass the argument

**Reason**: The conclusion has a |s.im|² denominator, so s.im ≠ 0 must be assumed. In the RH main proof, s is a nontrivial zero, so this assumption is trivial.

### 2. Project cleanup

- Deleted ~50 `stage_4_before_*.lean` old backups
- Deleted ~300 `build_*.txt` build logs
- Kept `stage_4.lean` (current working version) and `stage_4_before_h92_downgrade.lean` (clean rollback point)

## Current Status

**`mellin_rapid_decay_bound` theorem: 0 admits, fully closed.**

The entire stage_4.lean compiles successfully.

## Remaining Work

- The first 16 admits (lines 79–2687) are hard analysis, untouched
- The RH main proof `riemann_hypothesis` at line 5396 still depends on `sorryAx` (from earlier unclosed admits)

## Technical Lessons

1. **Line-by-line editing of proof blocks is infeasible**: repeatedly breaks proof structure (duplicate lines, misplaced `have`, variable shadowing). Must write the full block with Write and replace wholesale, or restore from backup.
2. **set/interval integral bridge**: `∫ Icc = ∫ Ioc = ∫ a..b`. Key lemmas: `integral_Icc_eq_integral_Ioc` + `intervalIntegral.integral_of_le`.
3. **`integral_rpow`** is a global name, not under the `intervalIntegral` namespace; takes `Or.inl h` or `Or.inr ...`.
4. **PowerShell background task limit**: accumulating many background build tasks causes "background shell task limit reached"; use Wait or switch to Python scripts.
