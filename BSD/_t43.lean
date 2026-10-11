import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import BSD.aE5_table_43

def aE5_43 (n : ℕ) : ℤ := if n ≤ 800 then aE5_raw_43 n else 0

-- T1: native_decide 单值（默认 maxRecDepth）
example : (0 : ℤ) ≤ aE5_43 1 := by native_decide

-- T2: norm_num [aE5_43] 只展开 wrapper（不展开表）
example : (aE5_43 1 : ℤ) = aE5_raw_43 1 := by norm_num [aE5_43]

-- T3: 37 版同款——nat cast 桥
example : (0 : ℝ) ≤ (aE5_43 1 : ℝ) := by
  have hz : (0 : ℤ) ≤ aE5_43 1 := by native_decide
  exact_mod_cast hz
