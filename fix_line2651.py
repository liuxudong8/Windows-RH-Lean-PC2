# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 修复 Line 2651 (index 2650) - gcongr 错误
print(f'Line 2651 before: {lines[2650].strip()}')

# 替换 gcongr 为手动证明
lines[2650] = '''    have h9 : (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2 ≤ 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) := by
      have h10 : 0 ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) := by positivity
      calc (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / |(nontrivialZeroEnum n).im| ^ 2
        ≤ (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) * (4 / (1 + |(nontrivialZeroEnum n).im|)^2) := by
          rw [div_le_div_iff (by positivity) (by positivity)] <;> nlinarith
      _ = 4 * ((zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|)^2) := by ring
    exact h9
'''

print(f'Line 2651 after: Fixed')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print('Done')
