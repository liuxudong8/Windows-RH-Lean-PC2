with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到第 2355 行附近（0-indexed: 2354）
for i in range(2350, 2360):
    print(f"{i+1}: {lines[i].rstrip()}")

# 修复第 2355 行（index 2354）
# 把 "rw [h_eq] <;> ring" 改为先 congrFun 再 ring
target_idx = 2354  # 第 2355 行
old_line = lines[target_idx]
print(f"\n目标行: {old_line.rstrip()}")

# 替换这一段
# 找到 h_decay' 证明块的开始
start_idx = None
for i in range(2348, 2358):
    if 'have h_decay' in lines[i]:
        start_idx = i
        break

print(f"开始行: {start_idx+1}")

# 替换从 start_idx 到 exact h_bound 行
new_block = '''  have h_decay' : ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s‖ ≤ C / (1 + |s.im|) ^ 2 := by
    intro s hre1' hre2'
    have h_eq : melinTransform f1.toTestFunction = melinTransform f2.toTestFunction + melinTransform h := h_m1_eq
    have h2 : melinTransform f1.toTestFunction s = melinTransform f2.toTestFunction s + melinTransform h s := by
      exact congrFun h_eq s
    have h1 : melinTransform f1.toTestFunction s - melinTransform f2.toTestFunction s = melinTransform h s := by
      rw [h2] <;> ring
    rw [h1]
    exact h_bound s hre1' hre2'
'''

# 找到结束行（exact h_bound）
end_idx = None
for i in range(start_idx, start_idx+15):
    if 'exact h_bound' in lines[i]:
        end_idx = i
        break

print(f"结束行: {end_idx+1}")

lines[start_idx:end_idx+1] = [new_block]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)

print("修复完成")
