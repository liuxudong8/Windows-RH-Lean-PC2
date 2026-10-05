f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- specDiscM 单射（由严格递增推出） -/
theorem specDiscM_injective : Function.Injective specDiscM := by
  intro m n h
  by_cases hmn : m < n
  · have h_lt : specDiscM m < specDiscM n := by
      induction' hmn with n hmn ih
      · exact specDiscM_strict_mono m
      · exact lt_trans ih (specDiscM_strict_mono n)
    linarith
  · by_cases hnm : n < m
    · have h_lt : specDiscM n < specDiscM m := by
        induction' hnm with m hnm ih
        · exact specDiscM_strict_mono n
        · exact lt_trans ih (specDiscM_strict_mono m)
      linarith
    · have h_eq : m = n := by omega
      exact h_eq"""

new = """/-- specDiscM 严格递增蕴含 m<n → specDiscM m < specDiscM n -/
theorem specDiscM_lt_of_lt {m n : ℕ} (h : m < n) : specDiscM m < specDiscM n := by
  induction n with
  | zero => exfalso; linarith
  | succ n ih =>
    by_cases hmn : m < n
    · exact lt_trans (ih hmn) (specDiscM_strict_mono n)
    · have h_eq : m = n := by omega
      rw [h_eq]
      exact specDiscM_strict_mono n

/-- specDiscM 单射（由严格递增推出） -/
theorem specDiscM_injective : Function.Injective specDiscM := by
  intro m n h
  by_cases hmn : m < n
  · have h_lt : specDiscM m < specDiscM n := specDiscM_lt_of_lt hmn
    linarith
  · by_cases hnm : n < m
    · have h_lt : specDiscM n < specDiscM m := specDiscM_lt_of_lt hnm
      linarith
    · have h_eq : m = n := by omega
      exact h_eq"""

content = content.replace(old, new, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: fixed specDiscM_injective proof')
