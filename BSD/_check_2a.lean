import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/- ②a 探针：E′ 群法则（加倍/加法）保持曲线 + 7 倍链真证。 -/

structure Eprime where
  X : ℚ
  Y : ℚ
  eqn : Y ^ 2 = X ^ 3 - 16 * X + 16

def Pprime : Eprime := ⟨0, 4, by norm_num⟩

def P2 : Eprime := ⟨4, 4, by norm_num⟩

def P3 : Eprime := ⟨-4, -4, by norm_num⟩

def P4 : Eprime := ⟨8, -20, by norm_num⟩

/-- 切点加倍（2P）：λ = (3x² − 16)/(2y)，x₃ = λ² − 2x，y₃ = λ(x − x₃) − y。 -/
def Eprime_double (P : Eprime) (hY : P.Y ≠ 0) : Eprime :=
  let lam : ℚ := (3 * P.X ^ 2 - 16) / (2 * P.Y)
  let x3 : ℚ := lam ^ 2 - 2 * P.X
  let y3 : ℚ := lam * (P.X - x3) - P.Y
  ⟨x3, y3, by
    simp only [x3, y3, lam]
    have h2y : (2 * P.Y : ℚ) ≠ 0 := by
      exact mul_ne_zero two_ne_zero hY
    field_simp [h2y]
    ring_nf
    rw [← sub_eq_zero]
    ring_nf
    have hE : P.Y ^ 2 - P.X ^ 3 + 16 * P.X - 16 = 0 := by
      rw [P.eqn]
      ring
    have hfac : P.X * P.Y ^ 6 * 1024 - P.X ^ 3 * P.Y ^ 6 * 64 - P.Y ^ 6 * 1024 + P.Y ^ 8 * 64 =
        64 * P.Y ^ 6 * (P.Y ^ 2 - P.X ^ 3 + 16 * P.X - 16) := by ring
    rw [hfac, hE]
    norm_num
  ⟩

/-- 2P′ = (4, 4)：加倍公式真证计算。 -/
example : Eprime_double Pprime (by norm_num [Pprime] : Pprime.Y ≠ 0) = P2 := by
  unfold Eprime_double Pprime P2
  congr 1 <;> norm_num

/-- 割线加法（P + Q，x₁ ≠ x₂）：λ = (y₂−y₁)/(x₂−x₁)，x₃ = λ² − x₁ − x₂，y₃ = λ(x₁−x₃) − y₁。 -/
def Eprime_add (P Q : Eprime) (hx : P.X ≠ Q.X) : Eprime :=
  let lam : ℚ := (Q.Y - P.Y) / (Q.X - P.X)
  let x3 : ℚ := lam ^ 2 - P.X - Q.X
  let y3 : ℚ := lam * (P.X - x3) - P.Y
  ⟨x3, y3, by
    simp only [x3, y3, lam]
    have hdx : (Q.X - P.X : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    field_simp [hdx]
    ring_nf
    rw [← sub_eq_zero]
    ring_nf
    rw [show P.Y ^ 3 = P.Y * P.Y ^ 2 by ring]
    rw [show Q.Y ^ 3 = Q.Y * Q.Y ^ 2 by ring]
    rw [show P.Y ^ 4 = (P.Y ^ 2) ^ 2 by ring]
    rw [show Q.Y ^ 4 = (Q.Y ^ 2) ^ 2 by ring]
    rw [P.eqn]
    rw [Q.eqn]
    ring
  ⟩

/-- 3P′ = 2P′ + P′ = (−4, −4)。 -/
example : Eprime_add P2 Pprime (by norm_num [P2, Pprime] : P2.X ≠ Pprime.X) = P3 := by
  unfold Eprime_add P2 P3 Pprime
  congr 1 <;> norm_num

/-- 4P′ = 3P′ + P′ = (8, −20)。 -/
example : Eprime_add P3 Pprime (by norm_num [P3, Pprime] : P3.X ≠ Pprime.X) = P4 := by
  unfold Eprime_add P3 P4 Pprime
  congr 1 <;> norm_num

def P5 : Eprime := ⟨1, -1, by norm_num⟩

def P6 : Eprime := ⟨24, 116, by norm_num⟩

def P7 : Eprime := ⟨-20 / 9, 172 / 27, by norm_num⟩

/-- 5P′ = 4P′ + P′ = (1, −1)。 -/
example : Eprime_add P4 Pprime (by norm_num [P4, Pprime] : P4.X ≠ Pprime.X) = P5 := by
  unfold Eprime_add P4 P5 Pprime
  congr 1 <;> norm_num

/-- 6P′ = 5P′ + P′ = (24, 116)。 -/
example : Eprime_add P5 Pprime (by norm_num [P5, Pprime] : P5.X ≠ Pprime.X) = P6 := by
  unfold Eprime_add P5 P6 Pprime
  congr 1 <;> norm_num

/-- 7P′ = 6P′ + P′ = (−20/9, 172/27)。 -/
example : Eprime_add P6 Pprime (by norm_num [P6, Pprime] : P6.X ≠ Pprime.X) = P7 := by
  unfold Eprime_add P6 P7 Pprime
  congr 1 <;> norm_num
