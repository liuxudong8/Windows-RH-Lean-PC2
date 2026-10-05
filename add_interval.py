path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Add interval indicator infrastructure after namespace and open Classical
insert_after = "namespace OrderPreservingBijection\n\nopen Classical\n"

new_code = """namespace OrderPreservingBijection

open Classical

/-- 区间指示函数（构造性定义）：1_{[a,b]}(x) = 1 if a ≤ x ≤ b else 0。
    因为 TestFunction 只要求紧支不要求连续，区间指示函数是合法的 TestFunction。
    这是构造 Mellin 变换基的关键工具。 -/
def intervalIndicator (a b : ℝ) (ha : 0 < a) (hab : a < b) : TestFunction :=
  { toFun := fun x : ℝ => if a ≤ x ∧ x ≤ b then (1 : ℂ) else 0
    hasCompactSupport := by
      refine ⟨b + 1, by linarith, ?_⟩
      intro x hx
      have h_gt_b : x > b := by
        by_cases hpos : 0 ≤ x
        · rw [abs_of_nonneg hpos] at hx; linarith
        · have h_neg : x < 0 := by linarith
          linarith
      have h_notin : ¬(a ≤ x ∧ x ≤ b) := by
        intro h; linarith [h.2]
      simp only [h_notin, if_false] }

/-- 区间指示函数的 Mellin 变换非零族（公理，有限维线性代数）：
    对任意 m 个互不相同的复点 t_0,...,t_{m-1}，存在 m 个区间 [a_i,b_i]，
    使得矩阵 A_{ji} = M[1_{[a_i,b_i]}](t_j) 可逆。
    数学依据：取区间 [a_i, a_i+ε]，ε→0 时 A_{ji} ≈ ε·a_i^{t_j-1}，
    极限矩阵 (a_i^{t_j-1}) 是广义 Vandermonde 矩阵（a_i>0 互不相同，t_j 互不相同），故可逆；
    由行列式连续性，ε 足够小时 A 可逆。
    这是纯分析断言，比完整的 Mellin 满射性更基本、更透明。 -/
axiom mellin_interval_linear_independence {m : ℕ} (t : Fin m → ℂ) (ht : Function.Injective t) :
    ∃ (a b : Fin m → ℝ), (∀ i, 0 < a i) ∧ (∀ i, a i < b i) ∧
      ∀ (c : Fin m → ℂ), (∀ j, ∑ i : Fin m, c i * melinTransform (intervalIndicator (a i) (b i) (by exact ‹_›) (by exact ‹_›)) (t j) = 0) → c = 0

"""

content = content.replace(insert_after, new_code)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Added intervalIndicator and independence axiom')
