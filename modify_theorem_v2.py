# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 修改定理陈述
old = '''theorem mellin_transform_C2_rapid_decay (h : MollifiedTestFunction) (B' : ℝ)
    (hC2 : ContDiff ℝ 2 h.toTestFunction.toFun)
    (hB : ∀ x, ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B') (hB_pos : 0 < B') :
    ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ 8 * B' * (globalR₀ ^ 3 + 1) / |s.im| ^ 2 := by'''

new = '''theorem mellin_transform_C2_rapid_decay (h : MollifiedTestFunction) (B' : ℝ)
    (hC2 : ContDiff ℝ 2 h.toTestFunction.toFun)
    (hB : ∀ x, ‖(deriv (deriv h.toTestFunction.toFun) x)‖ ≤ B') (hB_pos : 0 < B') :
    ∀ (s : ℂ), 0 < s.re → s.re < 1 →
      ‖melinTransform h.toTestFunction s‖ ≤ 32 * B' * (globalR₀ ^ 3 + 1) / (1 + |s.im|) ^ 2 := by'''

content = content.replace(old, new)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Done')
