# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 在 Line 2277 (index 2276) 后面添加新的引理
new_lemma = '''

lemma layer_sum_bound2 (C1 C2 : ℝ) (hC1_pos : 0 < C1) (hC2_pos : 0 < C2)
    (hC1 : ∀ (T : ℝ), 0 < T → Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat))
    (hC2 : ∀ (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)))
    (k : ℕ) (h_layer_fin : ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite) :
    ∑ n ∈ h_layer_fin.toFinset, ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2) ≤
    ((16 * C1 + 2) * (C2 * 4 + 1)) * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2
  let layer_k : Set ℕ := {n | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}
  have h_point : ∀ n ∈ layer_k, w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
    intro n hn
    have h_im1 : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| := hn.1
    have h_log : Real.log (2 + |(nontrivialZeroEnum n).im|) ≤ ((k : ℝ) + 2) * Real.log 2 := log_bound_for_layer k hn
    have h_m : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)) := hC2 n
    have h_m2 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := by
      calc _ ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)) := h_m
           _ ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := by gcongr
    have h_m3 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := by
      calc _ ≤ C2 * (1 + ((k : ℝ) + 2) * Real.log 2) := h_m2
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) := point_bound_algebra C2 hC2_pos k
    have h_denom : |(nontrivialZeroEnum n).im|^2 ≥ (2 : ℝ)^(2 * k) := by
      have h11 : |(nontrivialZeroEnum n).im|^2 ≥ ((2^k : ℝ))^2 := by gcongr
      rw [pow2_sq k] at h11; exact h11
    have h_w : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
      dsimp only [w]
      calc _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / |(nontrivialZeroEnum n).im|^2 := by gcongr
           _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by gcongr
    exact h_w
  have h_card : (h_layer_fin.toFinset.card : ℝ) ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h_card_raw := layer_card_bound_raw C1 hC1_pos hC1 k h_layer_fin
    have h_simp := card_bound_simplified C1 hC1_pos k
    linarith
  have h_sum1 : ∑ n ∈ h_layer_fin.toFinset, w n ≤ ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : n ∈ layer_k := (Set.Finite.mem_toFinset h_layer_fin).mp hn
    exact h_point n hn'
  have h_sum2 : ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) = (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by
    simp [Finset.sum_const] <;> ring
  have h_sum : ∑ n ∈ h_layer_fin.toFinset, w n ≤ (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by
    calc ∑ n ∈ h_layer_fin.toFinset, w n
      ≤ ∑ n ∈ h_layer_fin.toFinset, (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := h_sum1
      _ = (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := h_sum2
  have h_pos : (2 : ℝ)^k > 0 := by positivity
  calc ∑ n ∈ h_layer_fin.toFinset, w n
    ≤ (h_layer_fin.toFinset.card : ℝ) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := h_sum
    _ ≤ ((16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1)) * ((C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k)) := by gcongr
    _ = ((16 * C1 + 2) * (C2 * 4 + 1)) * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
      field_simp [h_pos.ne'] <;> ring
'''

# 在 Line 2277 (index 2276) 后面插入
lines.insert(2277, new_lemma)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
