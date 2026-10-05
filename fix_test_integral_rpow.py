# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\test_integral_rpow.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Line 82 是 sorry（0-indexed: 81）
print(f"Line 82: {lines[81].strip()}")

# 替换 Line 82
new_lines = [
    "      -- 变量替换：y = Real.log x，所以 x = Real.exp y，dx = Real.exp y dy\n",
    "      -- 我们需要证明：∫ x in ε₀..R₀, f (Real.log x) * (deriv Real.log x) dx = ∫ y in (Real.log ε₀)..(Real.log R₀), f y dy\n",
    "      -- 但是我们的被积函数是 Real.exp ((σ - 1) * Real.log x) = Real.exp ((σ - 1) * y)\n",
    "      -- 而 dx = Real.exp y dy\n",
    "      -- 所以我们需要用 intervalIntegral.integral_comp_mul\n",
    "      have h_le_log : Real.log ε₀ ≤ Real.log R₀ := Real.log_le_log (by linarith) (by linarith)\n",
    "      have h_cont : Continuous (fun y : ℝ => Real.exp (σ * y)) := by fun_prop\n",
    "      have h_ii : IntervalIntegrable (fun y : ℝ => Real.exp (σ * y)) MeasureTheory.volume (Real.log ε₀) (Real.log R₀) :=\n",
    "        h_cont.intervalIntegrable (Real.log ε₀) (Real.log R₀)\n",
    "      -- 变量替换定理：∫ x in ε₀..R₀, f (g x) * g' x dx = ∫ y in g ε₀..g R₀, f y dy\n",
    "      -- 其中 g x = Real.log x, f y = Real.exp (σ * y)\n",
    "      -- 注意：Real.exp ((σ - 1) * Real.log x) = Real.exp (σ * Real.log x) / x = f (g x) * g' x\n",
    "      have h_deriv_log : ∀ x ∈ Set.uIcc ε₀ R₀, HasDerivAt Real.log (1 / x) x := by\n",
    "        intro x hx\n",
    "        have hx_pos : 0 < x := by\n",
    "          have h5 : x ∈ Set.Icc ε₀ R₀ := by\n",
    "            rw [Set.uIcc_of_le h_le] at hx\n",
    "            exact hx\n",
    "          linarith [Set.mem_Icc.mp h5]\n",
    "        exact hasDerivAt_log hx_pos.ne'\n",
    "      have h_eq : ∫ x in ε₀..R₀, Real.exp ((σ - 1) * Real.log x) =\n",
    "          ∫ x in ε₀..R₀, (fun y : ℝ => Real.exp (σ * y)) (Real.log x) * (1 / x) := by\n",
    "        apply intervalIntegral.integral_congr\n",
    "        intro x hx\n",
    "        have hx_pos : 0 < x := by\n",
    "          have h5 : x ∈ Set.uIcc ε₀ R₀ := hx\n",
    "          have h6 : x ∈ Set.Icc ε₀ R₀ := by\n",
    "            rw [Set.uIcc_of_le h_le] at h5\n",
    "            exact h5\n",
    "          linarith [Set.mem_Icc.mp h6]\n",
    "        have h7 : Real.exp ((σ - 1) * Real.log x) = Real.exp (σ * Real.log x) / x := by\n",
    "          have h8 : Real.exp (σ * Real.log x) / x = Real.exp (σ * Real.log x) / Real.exp (Real.log x) := by\n",
    "            rw [Real.exp_log hx_pos]\n",
    "            <;> ring\n",
    "          rw [h8]\n",
    "          have h9 : Real.exp (σ * Real.log x) / Real.exp (Real.log x) = Real.exp (σ * Real.log x - Real.log x) := by\n",
    "            rw [← Real.exp_sub]\n",
    "            <;> ring\n",
    "          rw [h9]\n",
    "          have h10 : σ * Real.log x - Real.log x = (σ - 1) * Real.log x := by ring\n",
    "          rw [h10]\n",
    "        exact h7\n",
    "      rw [h_eq]\n",
    "      exact intervalIntegral.integral_comp_mul h_deriv_log h_ii\n"
]

# 替换 Line 82 之前的内容（从 Line 78 到 Line 82）
# 让我们找到正确的位置
for i in range(len(lines)):
    if 'sorry' in lines[i] and i > 70:
        print(f"Found sorry at line {i+1}")
        # 替换从 Line 78 到 Line i 的内容
        lines = lines[:77] + new_lines + lines[i+1:]
        break

with open(r'C:\proj2\OrderPreservingBijection\test_integral_rpow.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
