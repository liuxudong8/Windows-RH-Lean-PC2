import shutil

# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 要插入的新引理（在 point_bound_algebra 之后，zero_weighted_series_summable 之前）
new_lemmas = '''
lemma card_bound_simplified (C1 : ℝ) (hC1_pos : 0 < C1) (k : ℕ) :
    2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
  have h1 : (2^(k+1) : ℝ) + 1 ≤ 4 * (2 : ℝ)^k := by
    have h11 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    rw [h11]
    have h12 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h13 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h13
    linarith
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      norm_num at h2 ⊢; exact h2
    have h3 : Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (Real.exp 1) = 1 := by simp
    rw [h4] at h3; exact h3
  have h21 : (2^(k+1) : ℝ) + 2 ≤ (2^(k+2) : ℝ) := by
    have h22 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    have h23 : (2^(k+2) : ℝ) = 4 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
    rw [h22, h23]
    have h24 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h25 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h25
    linarith
  have h25 : (1 : ℝ) ≤ (2^(k+1) : ℝ) + 2 := by
    have h26 : (0 : ℝ) ≤ (2^(k+1) : ℝ) := by positivity
    have h27 : (2^(k+1) : ℝ) + 2 ≥ 2 := by linarith
    linarith
  have h_log_nonneg : 0 ≤ Real.log ((2^(k+1) : ℝ) + 2) := Real.log_nonneg h25
  have h23 : Real.log ((2^(k+1) : ℝ) + 2) ≤ Real.log (2^(k+2) : ℝ) := Real.log_le_log (by positivity) h21
  have h241 : Real.log (2^(k+2) : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have h242 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by simp
  have h24 : Real.log (2^(k+2) : ℝ) = ((k : ℝ) + 2) * Real.log 2 := by rw [h241, h242]
  have h27 : ((k : ℝ) + 2) ≤ 2 * ((k : ℝ) + 1) := by
    have h26 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
    linarith
  have h2 : Real.log ((2^(k+1) : ℝ) + 2) ≤ 2 * ((k : ℝ) + 1) := by
    calc Real.log ((2^(k+1) : ℝ) + 2)
      ≤ Real.log (2^(k+2) : ℝ) := h23
      _ = ((k : ℝ) + 2) * Real.log 2 := h24
      _ ≤ ((k : ℝ) + 2) * 1 := by gcongr
      _ ≤ 2 * ((k : ℝ) + 1) := by
        have h28 : ((k : ℝ) + 2) * 1 = (k : ℝ) + 2 := by ring
        rw [h28]; exact h27
  have h3 : 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1) ≤
           2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) := by
    gcongr <;> linarith
  have h4 : 2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) = 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 := by ring
  have h5 : (2 : ℝ) ≤ 2 * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h51 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h52 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h52
    have h53 : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
    nlinarith
  have h6 : 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := by
    have h7 : 2 ≤ 2 * (2 : ℝ)^k * ((k : ℝ) + 1) := h5
    nlinarith
  calc 2 * (C1 * ((2^(k+1) : ℝ) + 1) * Real.log ((2^(k+1) : ℝ) + 2) + 1)
    ≤ 2 * (C1 * (4 * (2 : ℝ)^k) * (2 * ((k : ℝ) + 1)) + 1) := h3
    _ = 16 * C1 * (2 : ℝ)^k * ((k : ℝ) + 1) + 2 := h4
    _ ≤ (16 * C1 + 2) * (2 : ℝ)^k * ((k : ℝ) + 1) := h6

lemma log_bound_for_layer (k : ℕ) {n : ℕ} (hn : (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)) :
    Real.log (2 + |(nontrivialZeroEnum n).im|) ≤ ((k : ℝ) + 2) * Real.log 2 := by
  have h_im2 : |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ) := hn.2
  have h_log1 : 2 + |(nontrivialZeroEnum n).im| ≤ (2^(k+2) : ℝ) := by
    have h : 2 + |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ) + 2 := by linarith
    have h2 : (2^(k+1) : ℝ) + 2 ≤ (2^(k+2) : ℝ) := by
      have h22 : (2^(k+1) : ℝ) = 2 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
      have h23 : (2^(k+2) : ℝ) = 4 * (2 : ℝ)^k := by simp [pow_succ] <;> ring
      rw [h22, h23]
      have h24 : (1 : ℝ) ≤ (2 : ℝ)^k := by have h25 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h25
      have h26 : 2 * (2 : ℝ)^k + 2 ≤ 4 * (2 : ℝ)^k := by
        have h27 : 2 ≤ 2 * (2 : ℝ)^k := by have h28 : (1 : ℝ) ≤ (2 : ℝ)^k := h24; linarith
        linarith
      exact h26
    linarith
  have h3 : Real.log (2 + |(nontrivialZeroEnum n).im|) ≤ Real.log (2^(k+2) : ℝ) := Real.log_le_log (by positivity) h_log1
  have h4 : Real.log (2^(k+2) : ℝ) = ((k : ℝ) + 2) * Real.log 2 := by
    have h41 : Real.log (2^(k+2) : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
    have h42 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by simp
    rw [h41, h42]
  rw [h4] at h3; exact h3

lemma pow2_sq (k : ℕ) : ((2^k : ℝ))^2 = (2 : ℝ)^(2 * k) := by
  have h13 : ((2^k : ℝ))^2 = (2 : ℝ)^(k * 2) := by rw [pow_mul]
  have h14 : k * 2 = 2 * k := by ring
  rw [h13, h14]

lemma layer_sum_bound (C1 C2 : ℝ) (hC1_pos : 0 < C1) (hC2_pos : 0 < C2)
    (hC1 : ∀ (T : ℝ), 0 < T → Set.encard {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} ≤ (Nat.ceil (C1 * (T + 1) * Real.log (T + 2)) : ENat))
    (hC2 : ∀ (n : ℕ), (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) ≤ C2 * (1 + Real.log (2 + |(nontrivialZeroEnum n).im|)))
    (k : ℕ) (h_layer_fin : ({n : ℕ | (2^k : ℝ) ≤ |(nontrivialZeroEnum n).im| ∧ |(nontrivialZeroEnum n).im| < (2^(k+1) : ℝ)}).Finite) :
    ∑ n ∈ h_layer_fin.toFinset, ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2) ≤
    ((16 * C1 + 2) * (C2 * 4 + 1)) * ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by
  let w : ℕ → ℝ := fun n => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2
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
    have h_denom : (1 + |(nontrivialZeroEnum n).im|)^2 ≥ (2 : ℝ)^(2 * k) := by
      have h8 : (1 : ℝ) ≤ (2^k : ℝ) := by have h9 : (1 : ℕ) ≤ 2^k := Nat.one_le_pow k 2 (by norm_num); exact_mod_cast h9
      have h10 : (1 : ℝ) ≤ |(nontrivialZeroEnum n).im| := by linarith
      have h11 : (1 + |(nontrivialZeroEnum n).im|)^2 ≥ ((2^k : ℝ))^2 := by nlinarith
      rw [pow2_sq k] at h11; exact h11
    have h_w : w n ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (2 : ℝ)^(2 * k) := by
      dsimp only [w]
      calc _ ≤ (C2 * 4 + 1) * ((k : ℝ) + 1) / (1 + |(nontrivialZeroEnum n).im|)^2 := by gcongr
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

# 在 "linarith" (point_bound_algebra 最后一行) 之后，"-- === 基础设施结束 ===" 之前插入
marker = '  linarith\n\n-- === 基础设施结束 ==='
if marker in content:
    content = content.replace(marker, '  linarith\n' + new_lemmas + '\n-- === 基础设施结束 ===')
    print("插入成功")
else:
    print("未找到标记点")

# 写入文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("文件已更新")
