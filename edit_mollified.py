# -*- coding: utf-8 -*-
# 替换 stage_4.lean 中 mollified_pair_tail_sum_negligible 为子类型版
# 范围：旧注释块（"/-- 磨光函数对的尾部和可忽略"）到旧证明末尾
import io, sys

path = r"c:\proj2\OrderPreservingBijection\stage_4.lean"
with io.open(path, "r", encoding="utf-8", newline="") as f:
    text = f.read()

start_marker = "/-- 磨光函数对的尾部和可忽略"
end_marker = "  exact \u27e8f1, f2, h_pts, h_m1, h_m2, h_summable_a, h_summable_b, h_final\u27e9"

si = text.find(start_marker)
ei = text.find(end_marker)
assert si != -1, "start marker not found"
assert ei != -1, "end marker not found"
ei_end = ei + len(end_marker)
assert ei_end <= len(text)

new_block = u"""/-- far 贡献对差的\u201c挖 \u03c1 拆分\u201d（admit，2026-10-01）：
    farZeroContribution f1 - farZeroContribution f2 = (\u03c1 项 if \u03c1 \u2208 farZeroSubtype) + \u2211' farDelta，
    其中 farDelta \u63d0\u53d6\u62d6\u8d70 \u03c1 \u9879\u3002\u6570\u5b66\u4f9d\u636e\uff1afarZeroContribution \u7684 tsum \u7ebf\u6027
    （Summable.sub\uff09+ \u5355\u70b9\u5206\u79bb\uff08HasSum \u6cbf\u65e0\u6761\u4ef6\u6ee4\u5b50\u6536\u655b\uff09\uff1b\u5404\u9879\u53ef\u548c\u65f6\u673a\u68b0\u53ef\u586b\uff0c
    \u672c\u5b9a\u7406\u5728 mollified_pair_tail_sum_negligible / off_critical_zero_tail_dominated \u7684\u53ef\u548c\u573a\u666f\u4f7f\u7528\u3002
    \u4e0d\u6d89\u53ca nontrivialZeroEnum \u679a\u4e3e\uff08:49 S \u65e0\u9650 sorry \u5df2\u6458\u9664\uff09\u3002 -/
theorem farContribution_pair_diff_split (f1 f2 : TestFunction) (\u03c1 : \u2102) :
    farZeroContribution f1 - farZeroContribution f2
      - (if \u03c1 \u2208 farZeroSubtype then (zeroMultiplicity \u03c1 : \u2102) else 0)
      = \u2211' \u03c1' : farZeroSubtype, (zeroMultiplicity \u03c1'.1 : \u2102) *
          (melinTransform f1 \u03c1'.1 - melinTransform f2 \u03c1'.1) * (if \u03c1'.1 = \u03c1 then 0 else 1) := by
  admit

/-- \u78e8\u5149\u51fd\u6570\u5bf9\u7684\u5c3e\u90e8\u548c\u53ef\u5ffd\u7565\uff08\u5b50\u7c7b\u578b\u7248\uff0c2026-10-01 \u91cd\u5199\uff09\uff1a\u5bf9\u975e\u4e34\u754c\u7ebf\u96f6\u70b9 \u03c1\uff0c
    \u5b58\u5728 f\u2081, f\u2082 \u4f7f\u5f97\uff1a
    (1) \u8c31\u70b9\u53d6\u503c\u76f8\u540c
    (2) M[f\u2081](\u03c1) = 1\uff0cM[f\u2082](\u03c1) = 0
    (3) \u56f4\u9053\u5185\uff08contourZeroFinset\uff09\u5176\u4f59\u96f6\u70b9\u4e0a M[f\u2081]=M[f\u2082]
    (4) \u56f4\u9053\u5916\uff08farZeroSubtype\uff09\u5dee\u7684\u201c\u6316 \u03c1 \u4f59\u9879\u201d\u7edd\u5bf9\u503c\u548c < m_\u03c1 / 2

    \u8bc1\u660e\u8def\u5f84\uff08\u4e0d\u518d\u4f9d\u8d56 nontrivialZeroEnum \u679a\u4e3e\uff09\uff1a
    (a) farZero_weighted_summable\uff1a\u2211 m(\u03c1')/|Im|\u00b2 \u6536\u655b\uff08\u5b50\u7c7b\u578b\uff0c\u96f6\u70b9\u5bc6\u5ea6\uff09
    (b) farZero_weighted_tail_small\uff1a\u6709\u9650\u96c6 F \u5916\u7684\u52a0\u6743\u4f59\u9879 < threshold\uff08\u53ef\u548c\u6027\u76f4\u63a5\u63a8\u8bba\uff09
    (c) T = contourZeroFinset\\{\u03c1} \u222a (F \u7684\u50cf \\ {\u03c1})\uff0cPWW \u6784\u9020 M[f\u2081]=M[f\u2082] \u5728 T \u4e0a
    (d) F \u5185\u8d21\u732e\u4e3a 0\uff08T \u4e0a\u76f8\u7b49\u6216\u6316 \u03c1\uff09\uff1bF \u5916\u8d21\u732e \u2264 C * w(\u03c1')
    (e) \u2016\u2211' farDelta\u2016 \u2264 C * (F \u5916\u4f59\u9879) < m_\u03c1/2\uff1bfar \u5dee\u7531 farContribution_pair_diff_split \u62c6\u9879 -/
theorem mollified_pair_tail_sum_negligible (\u03c1 : \u2102) :
    _root_.riemannZeta \u03c1 = 0 \u2192 0 < \u03c1.re \u2192 \u03c1.re < 1 \u2192 \u03c1.re \u2260 1 / 2 \u2192
    \u2203 (f1 f2 : MollifiedTestFunction),
      (\u2200 (n : \u2115), f1.toTestFunction.eval (specDiscM n) = f2.toTestFunction.eval (specDiscM n)) \u2227
      melinTransform f1.toTestFunction \u03c1 = 1 \u2227
      melinTransform f2.toTestFunction \u03c1 = 0 \u2227
      (\u2200 (\u03c1' : \u2102), \u03c1' \u2208 contourZeroFinset \u2192 \u03c1' \u2260 \u03c1 \u2192
        melinTransform f1.toTestFunction \u03c1' = melinTransform f2.toTestFunction \u03c1') \u2227
      Summable (fun (\u03c1' : farZeroSubtype) => (zeroMultiplicity \u03c1'.1 : \u2102) *
        (melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1) *
        (if \u03c1'.1 = \u03c1 then (0 : \u2102) else 1)) \u2227
      \u2016farZeroContribution f1.toTestFunction - farZeroContribution f2.toTestFunction
        - (if \u03c1 \u2208 farZeroSubtype then (zeroMultiplicity \u03c1 : \u2102) else 0)\u2016
        < (zeroMultiplicity \u03c1 : \u211d) / 2 := by
  intro hz hre1 hre2 hne
  -- (1) far \u6743\u91cd\u53ef\u548c
  have hw_nonneg : \u2200 \u03c1' : farZeroSubtype,
      0 \u2264 (zeroMultiplicity \u03c1'.1 : \u211d) / |\u03c1'.1.im| ^ 2 := by
    intro \u03c1'; apply div_nonneg <;> positivity
  have h_summable_w : Summable (fun \u03c1' : farZeroSubtype =>
      (zeroMultiplicity \u03c1'.1 : \u211d) / |\u03c1'.1.im| ^ 2) := farZero_weighted_summable
  have h_m\u03c1_pos : 0 < (zeroMultiplicity \u03c1 : \u211d) := by
    have h : 0 < zeroMultiplicity \u03c1 :=
      zeroMultiplicity_positive_at_nontrivial_zeros \u03c1 hz hre1 hre2
    exact_mod_cast h
  rcases mellin_pair_uniform_decay_bound \u03c1 hz hre1 hre2 hne with \u27e8C, hC_pos, h_uniform\u27e9
  set threshold : \u211d := (zeroMultiplicity \u03c1 : \u211d) / (2 * C) with hthreshold_def
  have h_threshold_pos : 0 < threshold := by
    rw [hthreshold_def]
    have hC_pos' : 0 < C := hC_pos
    have h_m\u03c1_pos' : 0 < (zeroMultiplicity \u03c1 : \u211d) := h_m\u03c1_pos
    positivity
  -- (2) \u6709\u9650\u903c\u8fd1 F
  rcases farZero_weighted_tail_small threshold h_threshold_pos with \u27e8F, h_rem\u27e9
  -- (3) \u6709\u9650 T = contourZeroFinset\\{\u03c1} \u222a (F \u50cf \\ {\u03c1})
  let Fimg : Set \u2102 := (Finset.image (fun \u03c1' : farZeroSubtype => \u03c1'.1) F : Set \u2102)
  let T0 : Set \u2102 := {\u03c1' | \u03c1' \u2208 contourZeroFinset \u2227 \u03c1' \u2260 \u03c1} \u222a (Fimg \\ {\u03c1})
  have hT0_finite : T0.Finite := by
    apply Set.Finite.union
    \u00b7 exact contourZeroFinset_finite.subset (by intro s hs; exact hs.1)
    \u00b7 exact (Finset.image (fun \u03c1' : farZeroSubtype => \u03c1'.1) F : Set \u2102).finite_toSet.subset (by intro s hs; exact hs.1)
  have h\u03c1_notin_T0 : \u03c1 \u2209 T0 := by
    intro h
    rcases h with h1 | h2
    \u00b7 exact h1.2 rfl
    \u00b7 exact h2.2 rfl
  rcases h_uniform T0 hT0_finite h\u03c1_notin_T0 with \u27e8f1, f2, h_pts, h_m1, h_m2, h_T_eq, h_decay\u27e9
  -- \u56f4\u9053\u5185\u6761\u4ef6\uff08T0 \u2287 contourZeroFinset\\{\u03c1}\uff09
  have h_fin_eq : \u2200 \u03c1' : \u2102, \u03c1' \u2208 contourZeroFinset \u2192 \u03c1' \u2260 \u03c1 \u2192
      melinTransform f1.toTestFunction \u03c1' = melinTransform f2.toTestFunction \u03c1' := by
    intro \u03c1' h\u03c1' hne'
    exact h_T_eq \u03c1' (Or.inl \u27e8h\u03c1', hne'\u27e9)
  -- (4) far \u5dee\u9879\uff08\u6316 \u03c1\uff09\u4e0e F \u5185\u5916\u5206\u89e3
  let farDelta : farZeroSubtype \u2192 \u2102 := fun \u03c1' =>
    (zeroMultiplicity \u03c1'.1 : \u2102) *
      (melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1) *
      (if \u03c1'.1 = \u03c1 then (0 : \u2102) else 1)
  let w\u03b4F : farZeroSubtype \u2192 \u211d := fun \u03c1' =>
    (zeroMultiplicity \u03c1'.1 : \u211d) / |\u03c1'.1.im| ^ 2 * (if \u03c1'.1 = \u03c1 then 0 else 1) *
      (if \u03c1' \u2208 F then 0 else 1)
  have hw\u03b4F_nonneg : \u2200 \u03c1', 0 \u2264 w\u03b4F \u03c1' := by
    intro \u03c1'
    dsimp [w\u03b4F]
    apply mul_nonneg <;> positivity
  have h_summable_w\u03b4F : Summable w\u03b4F := by
    apply Summable.of_nonneg_of_le hw\u03b4F_nonneg
    \u00b7 intro \u03c1'
      dsimp [w\u03b4F]
      by_cases h\u03c1 : \u03c1'.1 = \u03c1 <;> by_cases hF : \u03c1' \u2208 F <;> simp [h\u03c1, hF] <;> linarith [hw_nonneg \u03c1']
    \u00b7 intro \u03c1'
      dsimp [w\u03b4F]
      by_cases h\u03c1 : \u03c1'.1 = \u03c1 <;> by_cases hF : \u03c1' \u2208 F <;> simp [h\u03c1, hF] <;> exact hw_nonneg \u03c1'
    \u00b7 exact h_summable_w
  -- \u2016farDelta\u2016 \u2264 C * w\u03b4F\uff08F \u5185 farDelta = 0\uff1aT \u4e0a\u76f8\u7b49\u6216\u6316 \u03c1\uff09
  have h_norm_delta_bound : \u2200 \u03c1', \u2016farDelta \u03c1'\u2016 \u2264 C * w\u03b4F \u03c1' := by
    intro \u03c1'
    by_cases hF : \u03c1' \u2208 F
    \u00b7 -- F \u5185\uff1afarDelta = 0
      have h0 : farDelta \u03c1' = 0 := by
        by_cases h\u03c1 : \u03c1'.1 = \u03c1
        \u00b7 simp [farDelta, h\u03c1]
        \u00b7 -- \u03c1'.1 \u2208 Fimg \\ {\u03c1} \u2286 T0 \u27f9 \u0394M = 0
          have hT : \u03c1'.1 \u2208 T0 := by
            right
            exact \u27e8Finset.mem_image.mpr \u27e8\u03c1', hF, rfl\u27e9, h\u03c1\u27e9
          have h_eq : melinTransform f1.toTestFunction \u03c1'.1 = melinTransform f2.toTestFunction \u03c1'.1 :=
            h_T_eq \u03c1'.1 hT
          simp [farDelta, h\u03c1, h_eq]
      rw [h0]
      have h_nonneg : 0 \u2264 C * w\u03b4F \u03c1' :=
        mul_nonneg (le_of_lt hC_pos) (hw\u03b4F_nonneg \u03c1')
      simpa using h_nonneg
    \u00b7 -- F \u5916\uff1aw\u03b4F = w\u00b7(if \u03c1'=\u03c1)\uff1bh_decay \u7ed9\u5355\u9879\u754c
      by_cases h\u03c1 : \u03c1'.1 = \u03c1
      \u00b7 -- \u6316 \u03c1\uff1afarDelta = 0
        have h0 : farDelta \u03c1' = 0 := by simp [farDelta, h\u03c1]
        rw [h0]
        have h_nonneg : 0 \u2264 C * w\u03b4F \u03c1' :=
          mul_nonneg (le_of_lt hC_pos) (hw\u03b4F_nonneg \u03c1')
        simpa using h_nonneg
      \u00b7 -- \u975e \u03c1\uff1ah_decay
        have hz' : _root_.riemannZeta \u03c1'.1 = 0 := \u03c1'.2.1
        have hre1' : 0 < \u03c1'.1.re := \u03c1'.2.2.1
        have hre2' : \u03c1'.1.re < 1 := \u03c1'.2.2.2.1
        have him : \u03c1'.1.im \u2260 0 := nontrivialZero_im_ne_zero \u03c1'.1 hz' hre1' hre2'
        have h_d : \u2016melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1\u2016 \u2264 C / |\u03c1'.1.im| ^ 2 :=
          h_decay \u03c1'.1 hre1' hre2' him
        have h_norm_le : \u2016farDelta \u03c1'\u2016 \u2264 (zeroMultiplicity \u03c1'.1 : \u211d) *
            \u2016melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1\u2016 := by
          calc
            \u2016farDelta \u03c1'\u2016 = \u2016(zeroMultiplicity \u03c1'.1 : \u2102) *
                (melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1)\u2016 := by
              dsimp [farDelta]
              simp [h\u03c1]
            _ \u2264 \u2016(zeroMultiplicity \u03c1'.1 : \u2102)\u2016 *
                \u2016melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1\u2016 := norm_mul_le _ _
            _ = (zeroMultiplicity \u03c1'.1 : \u211d) *
                \u2016melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1\u2016 := by
              rw [norm_natCast]
        calc
          \u2016farDelta \u03c1'\u2016 \u2264 (zeroMultiplicity \u03c1'.1 : \u211d) *
              \u2016melinTransform f1.toTestFunction \u03c1'.1 - melinTransform f2.toTestFunction \u03c1'.1\u2016 := h_norm_le
          _ \u2264 (zeroMultiplicity \u03c1'.1 : \u211d) * (C / |\u03c1'.1.im| ^ 2) := by gcongr
          _ = C * w\u03b4F \u03c1' := by
            dsimp [w\u03b4F]
            simp [hF, h\u03c1] <;> ring
  have h_summable_Cw\u03b4F : Summable (fun \u03c1' => C * w\u03b4F \u03c1') := Summable.mul_left C h_summable_w\u03b4F
  have h_summable_norm_delta : Summable (fun \u03c1' => \u2016farDelta \u03c1'\u2016) :=
    Summable.of_nonneg_of_le (fun \u03c1' => by positivity) h_norm_delta_bound h_summable_Cw\u03b4F
  have h_summable_farDelta : Summable farDelta := Summable.of_norm h_summable_norm_delta
  -- (5) \u5c3e\u90e8\u754c\uff1a\u2211'\u2016farDelta\u2016 \u2264 C\u00b7\u2211'w\u03b4F \u2264 C\u00b7(F \u5916\u4f59\u9879) < C\u00b7threshold = m/2
  have h_sum_delta_le : \u2211' \u03c1', \u2016farDelta \u03c1'\u2016 \u2264 C * \u2211' \u03c1', w\u03b4F \u03c1' := by
    apply Summable.tsum_le_tsum h_norm_delta_bound h_summable_norm_delta h_summable_Cw\u03b4F
  have h_w\u03b4F_le_out : \u2211' \u03c1', w\u03b4F \u03c1' \u2264 \u2211' \u03c1',
      (if \u03c1' \u2208 F then (0 : \u211d) else (zeroMultiplicity \u03c1'.1 : \u211d) / |\u03c1'.1.im| ^ 2) := by
    apply Summable.tsum_le_tsum
    \u00b7 intro \u03c1'
      dsimp [w\u03b4F]
      by_cases hF : \u03c1' \u2208 F <;> by_cases h\u03c1 : \u03c1'.1 = \u03c1 <;> simp [hF, h\u03c1] <;> linarith [hw_nonneg \u03c1']
    \u00b7 exact h_summable_w\u03b4F
    \u00b7 have h_rem_sum : Summable (fun \u03c1' : farZeroSubtype => (if \u03c1' \u2208 F then (0 : \u211d) else
          (zeroMultiplicity \u03c1'.1 : \u211d) / |\u03c1'.1.im| ^ 2)) := by
        apply Summable.of_nonneg_of_le
        \u00b7 intro \u03c1'; by_cases h : \u03c1' \u2208 F <;> simp [h]; apply div_nonneg <;> positivity
        \u00b7 intro \u03c1'; by_cases h : \u03c1' \u2208 F <;> simp [h] <;> exact hw_nonneg \u03c1'
        \u00b7 exact h_summable_w
      exact h_rem_sum
  have h_sum_delta_lt : \u2211' \u03c1', \u2016farDelta \u03c1'\u2016 < C * threshold := by
    calc
      \u2211' \u03c1', \u2016farDelta \u03c1'\u2016 \u2264 C * \u2211' \u03c1', w\u03b4F \u03c1' := h_sum_delta_le
      _ \u2264 C * \u2211' \u03c1', (if \u03c1' \u2208 F then (0 : \u211d) else (zeroMultiplicity \u03c1'.1 : \u211d) / |\u03c1'.1.im| ^ 2) := by gcongr
      _ < C * threshold := by
        gcongr
        exact h_rem
  have h_sum_delta_bound : \u2211' \u03c1', \u2016farDelta \u03c1'\u2016 < (zeroMultiplicity \u03c1 : \u211d) / 2 := by
    have h_calc : C * threshold = (zeroMultiplicity \u03c1 : \u211d) / 2 := by
      rw [hthreshold_def]
      field_simp [hC_pos.ne'] <;> ring
    calc
      \u2211' \u03c1', \u2016farDelta \u03c1'\u2016 < C * threshold := h_sum_delta_lt
      _ = (zeroMultiplicity \u03c1 : \u211d) / 2 := h_calc
  -- (6) far \u5dee\u754c\uff08farContribution_pair_diff_split + \u4e09\u89d2\uff09
  have h_split := farContribution_pair_diff_split f1.toTestFunction f2.toTestFunction \u03c1
  have h_norm_tsum_delta : \u2016\u2211' \u03c1', farDelta \u03c1'\u2016 \u2264 \u2211' \u03c1', \u2016farDelta \u03c1'\u2016 :=
    norm_tsum_le_tsum_norm h_summable_farDelta
  have h_tail_lt : \u2016farZeroContribution f1.toTestFunction - farZeroContribution f2.toTestFunction
      - (if \u03c1 \u2208 farZeroSubtype then (zeroMultiplicity \u03c1 : \u2102) else 0)\u2016
      < (zeroMultiplicity \u03c1 : \u211d) / 2 := by
    rw [h_split]
    exact lt_of_le_of_lt h_norm_tsum_delta h_sum_delta_bound
  exact \u27e8f1, f2, h_pts, h_m1, h_m2, h_fin_eq, h_summable_farDelta, h_tail_lt\u27e9
"""

new_text = text[:si] + new_block + text[ei_end:]
with io.open(path, "w", encoding="utf-8", newline="") as f:
    f.write(new_text)
print("OK replaced; block chars:", len(new_block))
