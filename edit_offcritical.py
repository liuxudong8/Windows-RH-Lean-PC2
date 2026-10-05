# -*- coding: utf-8 -*-
import io
path = r"c:\proj2\OrderPreservingBijection\stage_4.lean"
with io.open(path, "r", encoding="utf-8", newline="") as f:
    text = f.read()

start_marker = "/-- 非临界线零点的尾部贡献主导性"
end_marker = "  exact \u27e8f1, f2, h_pts, h_m1, h_m2, h_final\u27e9"
si = text.find(start_marker)
ei = text.find(end_marker)
assert si != -1, "start not found"
assert ei != -1, "end not found"
ei_end = ei + len(end_marker)

new_block = u"""/-- 非临界线零点的尾部贡献主导性（子类型版，2026-10-01 重写）：由 mollified 尾部和可忽略
    + 围道内/外两分支拆分 + 三角不等式推出。不再依赖 nontrivialZeroEnum 枚举（:49 已摘除）。 -/
theorem off_critical_zero_tail_dominated (\u03c1 : \u2102) :
    _root_.riemannZeta \u03c1 = 0 \u2192 0 < \u03c1.re \u2192 \u03c1.re < 1 \u2192 \u03c1.re \u2260 1 / 2 \u2192
    \u2203 (f1 f2 : MollifiedTestFunction),
      (\u2200 (n : \u2115), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) \u2227
      melinTransform f1.toTestFunction \u03c1 = 1 \u2227
      melinTransform f2.toTestFunction \u03c1 = 0 \u2227
      nontrivialZeroSum f1.toTestFunction \u2260 nontrivialZeroSum f2.toTestFunction := by
  intro hz hre1 hre2 hne
  rcases mollified_pair_tail_sum_negligible \u03c1 hz hre1 hre2 hne with
    \u27e8f1, f2, h_pts, h_m1, h_m2, h_fin_eq, h_summable_delta, h_tail\u27e9
  -- (1) \u56f4\u9053\u5185 Finset \u5dee = (if \u03c1 \u2208 contourZeroFinset then m(\u03c1) else 0)
  have h_fin_diff : (\u2211 \u03c1' \u2208 contourZeroFinset, (zeroMultiplicity \u03c1' : \u2102) * melinTransform f1.toTestFunction \u03c1')
      - (\u2211 \u03c1' \u2208 contourZeroFinset, (zeroMultiplicity \u03c1' : \u2102) * melinTransform f2.toTestFunction \u03c1')
      = (if \u03c1 \u2208 contourZeroFinset then (zeroMultiplicity \u03c1 : \u2102) else 0) := by
    by_cases h\u03c1in : \u03c1 \u2208 contourZeroFinset
    \u00b7 let g1 : \u2102 \u2192 \u2102 := fun \u03c1' => (zeroMultiplicity \u03c1' : \u2102) * melinTransform f1.toTestFunction \u03c1'
      let g2 : \u2102 \u2192 \u2102 := fun \u03c1' => (zeroMultiplicity \u03c1' : \u2102) * melinTransform f2.toTestFunction \u03c1'
      have h_rest : \u2200 \u03c1' \u2208 contourZeroFinset.erase \u03c1, g1 \u03c1' = g2 \u03c1' := by
        intro \u03c1' h\u03c1'
        have h\u03c1'c : \u03c1' \u2208 contourZeroFinset := (Finset.mem_erase.mp h\u03c1').1
        have hne' : \u03c1' \u2260 \u03c1 := (Finset.mem_erase.mp h\u03c1').2
        dsimp [g1, g2]
        rw [h_fin_eq \u03c1' h\u03c1'c hne'] <;> ring
      have h_e1 : (\u2211 \u03c1' \u2208 contourZeroFinset, g1 \u03c1') = g1 \u03c1 + (\u2211 \u03c1' \u2208 contourZeroFinset.erase \u03c1, g1 \u03c1') := by
        simpa [add_comm] using (Finset.sum_erase_add (s := contourZeroFinset) (a := \u03c1) (f := g1) h\u03c1in).symm
      have h_e2 : (\u2211 \u03c1' \u2208 contourZeroFinset, g2 \u03c1') = g2 \u03c1 + (\u2211 \u03c1' \u2208 contourZeroFinset.erase \u03c1, g2 \u03c1') := by
        simpa [add_comm] using (Finset.sum_erase_add (s := contourZeroFinset) (a := \u03c1) (f := g2) h\u03c1in).symm
      have h_erase_eq : (\u2211 \u03c1' \u2208 contourZeroFinset.erase \u03c1, g1 \u03c1') = (\u2211 \u03c1' \u2208 contourZeroFinset.erase \u03c1, g2 \u03c1') := by
        rw [Finset.sum_congr rfl h_rest]
      have h_g1\u03c1 : g1 \u03c1 = (zeroMultiplicity \u03c1 : \u2102) := by
        dsimp [g1]
        rw [h_m1] <;> ring
      have h_g2\u03c1 : g2 \u03c1 = 0 := by
        dsimp [g2]
        rw [h_m2] <;> ring
      have h_calc : (\u2211 \u03c1' \u2208 contourZeroFinset, g1 \u03c1') - (\u2211 \u03c1' \u2208 contourZeroFinset, g2 \u03c1') = (zeroMultiplicity \u03c1 : \u2102) := by
        calc
          (\u2211 \u03c1' \u2208 contourZeroFinset, g1 \u03c1') - (\u2211 \u03c1' \u2208 contourZeroFinset, g2 \u03c1')
              = (g1 \u03c1 + \u2211 \u03c1' \u2208 contourZeroFinset.erase \u03c1, g1 \u03c1') - (g2 \u03c1 + \u2211 \u03c1' \u2208 contourZeroFinset.erase \u03c1, g2 \u03c1') := by rw [h_e1, h_e2]
          _ = g1 \u03c1 - g2 \u03c1 := by rw [h_erase_eq] <;> ring
          _ = (zeroMultiplicity \u03c1 : \u2102) := by rw [h_g1\u03c1, h_g2\u03c1] <;> ring
      simpa [h\u03c1in] using h_calc
    \u00b7 let g1 : \u2102 \u2192 \u2102 := fun \u03c1' => (zeroMultiplicity \u03c1' : \u2102) * melinTransform f1.toTestFunction \u03c1'
      let g2 : \u2102 \u2192 \u2102 := fun \u03c1' => (zeroMultiplicity \u03c1' : \u2102) * melinTransform f2.toTestFunction \u03c1'
      have h_all : \u2200 \u03c1' \u2208 contourZeroFinset, g1 \u03c1' = g2 \u03c1' := by
        intro \u03c1' h\u03c1'
        have hne' : \u03c1' \u2260 \u03c1 := by
          intro h'
          rw [h'] at h\u03c1'
          exact h\u03c1in h\u03c1'
        dsimp [g1, g2]
        rw [h_fin_eq \u03c1' h\u03c1' hne'] <;> ring
      have h_eq : (\u2211 \u03c1' \u2208 contourZeroFinset, g1 \u03c1') = (\u2211 \u03c1' \u2208 contourZeroFinset, g2 \u03c1') := by
        rw [Finset.sum_congr rfl h_all]
      have h_zero : (\u2211 \u03c1' \u2208 contourZeroFinset, g1 \u03c1') - (\u2211 \u03c1' \u2208 contourZeroFinset, g2 \u03c1') = 0 := by
        rw [h_eq] <;> ring
      simpa [h\u03c1in] using h_zero
  -- (2) far \u5dee\u62c6 \u03c1 \u9879\uff08farContribution_pair_diff_split\uff09
  let farDelta : farZeroSubtype \u2192 \u2102 := fun \u03c1' =>
    (zeroMultiplicity \u03c1'.1 : \u2102) *
      (melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1) *
      (if \u03c1'.1 = \u03c1 then (0 : \u2102) else 1)
  have h_split_far : farZeroContribution f1.toTestFunction - farZeroContribution f2.toTestFunction
      = (if IsFarZero \u03c1 then (zeroMultiplicity \u03c1 : \u2102) else 0)
        + (\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1') := by
    rw [\u2190 farContribution_pair_diff_split f1.toTestFunction f2.toTestFunction \u03c1]
    ring
  -- (3) \u03c1 \u2208 contourZeroFinset \u27fa \u03c1 \u2209 far\uff08\u4e92\u65a5\u5b8c\u5907\uff09
  have h_excl : (if \u03c1 \u2208 contourZeroFinset then (zeroMultiplicity \u03c1 : \u2102) else 0)
      + (if IsFarZero \u03c1 then (zeroMultiplicity \u03c1 : \u2102) else 0)
      = (zeroMultiplicity \u03c1 : \u2102) := by
    by_cases hc : \u2016\u03c1 - (1 / 2 : \u2102)\u2016 < 1
    \u00b7 have h\u03c1in_c : \u03c1 \u2208 contourZeroFinset := (contourZeroFinset_mem \u03c1).mpr \u27e8hz, hre1, hre2, hc\u27e9
      have h\u03c1not_far : \u00ac IsFarZero \u03c1 := by
        intro h
        have hge : \u2016\u03c1 - (1 / 2 : \u2102)\u2016 \u2265 1 := h.2.2.2
        linarith
      simp [h\u03c1in_c, h\u03c1not_far]
    \u00b7 have hge : \u2016\u03c1 - (1 / 2 : \u2102)\u2016 \u2265 1 := le_of_not_gt hc
      have h\u03c1in_f : IsFarZero \u03c1 := \u27e8hz, hre1, hre2, hge\u27e9
      have h\u03c1not_c : \u03c1 \u2209 contourZeroFinset := by
        intro h
        have hl : \u2016\u03c1 - (1 / 2 : \u2102)\u2016 < 1 := (contourZeroFinset_mem \u03c1).mp h |>.2.2.2
        linarith
      simp [h\u03c1not_c, h\u03c1in_f]
  -- (4) \u603b\u5dee = m(\u03c1) + \u2211'farDelta
  have h_total_eq : nontrivialZeroSum f1.toTestFunction - nontrivialZeroSum f2.toTestFunction
      = (zeroMultiplicity \u03c1 : \u2102) + (\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1') := by
    unfold nontrivialZeroSum
    rw [h_fin_diff, h_split_far, h_excl]
    ring
  -- (5) \u5c3e\u90e8\u754c\uff08\u6539\u5199\u4e3a farDelta \u7684 tsum\uff09
  have h_tail' : \u2016\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1'\u2016 < (zeroMultiplicity \u03c1 : \u211d) / 2 := by
    rw [\u2190 farContribution_pair_diff_split f1.toTestFunction f2.toTestFunction \u03c1] at h_tail
    exact h_tail
  -- (6) \u4e3b\u77db\u76fe\uff1a\u82e5\u603b\u5dee = 0 \u27f9 \u2211'farDelta = -m(\u03c1) \u27f9 \u2016\u2211'farDelta\u2016 = m(\u03c1) > m/2\uff0c\u4e0e (5) \u77db\u76fe
  have h_main : nontrivialZeroSum f1.toTestFunction \u2260 nontrivialZeroSum f2.toTestFunction := by
    intro h
    have h_diff : nontrivialZeroSum f1.toTestFunction - nontrivialZeroSum f2.toTestFunction = 0 := by
      rw [h] <;> ring
    have h_zero_total : (zeroMultiplicity \u03c1 : \u2102) + (\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1') = 0 := by
      rw [h_total_eq] at h_diff
      exact h_diff
    have h_small : (\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1') = -((zeroMultiplicity \u03c1 : \u2102)) := by
      calc
        (\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1')
            = (zeroMultiplicity \u03c1 : \u2102) + (\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1') - (zeroMultiplicity \u03c1 : \u2102) := by ring
        _ = 0 - (zeroMultiplicity \u03c1 : \u2102) := by rw [h_zero_total]
        _ = -((zeroMultiplicity \u03c1 : \u2102)) := by ring
    have h_small_norm : \u2016\u2211' \u03c1' : farZeroSubtype, farDelta \u03c1'\u2016 = (zeroMultiplicity \u03c1 : \u211d) := by
      rw [h_small]
      simp [norm_neg]
      rw [norm_natCast]
    have h_contra : (zeroMultiplicity \u03c1 : \u211d) < (zeroMultiplicity \u03c1 : \u211d) / 2 := by
      rw [\u2190 h_small_norm]
      exact h_tail'
    have hm : 0 < (zeroMultiplicity \u03c1 : \u211d) := by
      have h : 0 < zeroMultiplicity \u03c1 := zeroMultiplicity_positive_at_nontrivial_zeros \u03c1 hz hre1 hre2
      exact_mod_cast h
    linarith
  exact \u27e8f1, f2, h_pts, h_m1, h_m2, h_main\u27e9
"""

new_text = text[:si] + new_block + text[ei_end:]
with io.open(path, "w", encoding="utf-8", newline="") as f:
    f.write(new_text)
print("OK off_critical replaced; chars:", len(new_block))
