import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/- ②b 探针：X³ − 16X + 16 无 ℚ 根（E′[2] = {O} 的核心）。
   证明路线：有理根定理（首项 1）——r = n/d（互素）⟹ d | n³ ⟹ d | 1 ⟹ d = 1
   ⟹ r = n ∈ ℤ；n | 16 ⟹ |n| ≤ 16 ⟹ interval_cases 枚举，逐 case norm_num 排除。 -/
example (r : ℚ) (hr : r ^ 3 - 16 * r + 16 = 0) : False := by
  cases r with
  | div n d nonzero coprime =>
    -- r = n / d，nonzero : d ≠ 0，coprime : n.natAbs.Coprime d
    have hdz : (d : ℚ) ≠ 0 := by exact_mod_cast nonzero
    have hmul := congrArg (fun t : ℚ => t * (d : ℚ) ^ 3) hr
    have hzq : (n : ℚ) ^ 3 - 16 * (n : ℚ) * (d : ℚ) ^ 2 + 16 * (d : ℚ) ^ 3 = 0 := by
      field_simp [hdz] at hmul
      ring_nf at hmul ⊢
      exact hmul
    have hz : (n : ℤ) ^ 3 - 16 * n * (d : ℤ) ^ 2 + 16 * (d : ℤ) ^ 3 = 0 := by
      exact_mod_cast hzq
    -- d | n³（ℤ）：
    have hdvd : (d : ℤ) ∣ (n : ℤ) ^ 3 := by
      use 16 * (d : ℤ) * (n - d)
      nlinarith [hz]
    -- ℕ 上 d | n.natAbs³：
    have hdvdN : d ∣ n.natAbs ^ 3 := by
      rcases hdvd with ⟨k, hk⟩
      have habsd : |(d : ℤ)| = (d : ℤ) := by
        rw [abs_of_nonneg]
        exact_mod_cast (Nat.zero_le d)
      have hkabs : (d : ℤ) * |k| = (n.natAbs ^ 3 : ℤ) := by
        calc
          (d : ℤ) * |k| = |(d : ℤ)| * |k| := by rw [habsd]
          _ = |(d : ℤ) * k| := by rw [abs_mul]
          _ = |(n : ℤ) ^ 3| := by rw [hk]
          _ = (n.natAbs ^ 3 : ℤ) := by simp
      exact (Int.natCast_dvd_natCast.mp ⟨|k|, hkabs.symm⟩)
    -- 互素 ⟹ d | n.natAbs（两步剥离平方因子）：
    have hdvdna : d ∣ n.natAbs := by
      have hdn : d ∣ n.natAbs * (n.natAbs ^ 2) := by
        rw [pow_succ, mul_comm] at hdvdN
        exact hdvdN
      have h1 : d ∣ n.natAbs ^ 2 := by
        exact (coprime.symm.dvd_of_dvd_mul_left hdn)
      have hd2 : d ∣ n.natAbs * n.natAbs := by
        rw [pow_two] at h1
        exact h1
      exact (coprime.symm.dvd_of_dvd_mul_left hd2)
    -- d | n.natAbs 且互素 ⟹ d = 1：
    have hd1 : d = 1 := by
      have hgcd1 : n.natAbs.gcd d = 1 := coprime
      have hgcdd : d.gcd n.natAbs = d := Nat.gcd_eq_left hdvdna
      have hgcdd' : n.natAbs.gcd d = d := by rw [Nat.gcd_comm]; exact hgcdd
      rw [hgcdd'] at hgcd1
      exact hgcd1
    -- f(n) = 0（ℚ 与 ℤ）：
    have hfnq : (n : ℚ) ^ 3 - 16 * (n : ℚ) + 16 = 0 := by
      simpa [hd1] using hr
    have hfnz : (n : ℤ) ^ 3 - 16 * n + 16 = 0 := by
      exact_mod_cast hfnq
    -- n | 16：
    have hd16 : n ∣ (16 : ℤ) := by
      use -(n ^ 2 - 16)
      nlinarith [hfnz]
    -- |n| ≤ 16：
    have hle : |n| ≤ 16 := by
      rcases hd16 with ⟨k, hk⟩
      have hk' : n * k = 16 := hk.symm
      have hnz : n ≠ 0 := by
        intro hn
        rw [hn, zero_mul] at hk'
        norm_num at hk'
      have hkz : k ≠ 0 := by
        intro hk0
        rw [hk0, mul_zero] at hk'
        norm_num at hk'
      have hk1 : (1 : ℤ) ≤ |k| := by
        exact Int.one_le_abs hkz
      have habs : |n| * |k| = 16 := by
        calc
          |n| * |k| = |n * k| := by rw [abs_mul]
          _ = |16| := by rw [hk']
          _ = 16 := by norm_num
      have hnnonneg : 0 ≤ |n| := abs_nonneg n
      have hmul : |n| ≤ |n| * |k| := by
        simpa using mul_le_mul_of_nonneg_left hk1 hnnonneg
      calc
        |n| ≤ |n| * |k| := hmul
        _ = 16 := habs
    -- 界 → interval_cases：
    have hcc : n ∈ Set.Icc (-16 : ℤ) 16 := by
      rw [Set.mem_Icc]
      exact abs_le.mp hle
    have hlo : (-16 : ℤ) ≤ n := hcc.1
    have hhi : n ≤ 16 := hcc.2
    interval_cases n <;> norm_num at hfnz
