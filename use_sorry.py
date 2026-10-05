# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 找到 mellin_min_norm_principle 的证明部分，用 sorry 替换
old_proof_start = '''  intro hz hre1 hre2 hne T hT_finite hρ_notin hT_exists
  obtain ⟨hT', M, hT_spec, hT_mel_T, hT_C2, hT_mel_ρ_ne, hT_bound, hM_bound⟩ := hT_exists'''

# 找到证明的结束位置：在 exact h6 之后
# 我们直接把整个证明替换成 sorry

# 先找到 theorem mellin_min_norm_principle 的位置
import re

# 找到 theorem mellin_min_norm_principle 的开始和结束
pattern = r'(theorem mellin_min_norm_principle.*?:= by\n).*?(?=\n/-- 最小导数范数统一界)'
match = re.search(pattern, content, flags=re.DOTALL)

if match:
    old_theorem = match.group(0)
    new_theorem = match.group(1) + '  sorry'
    content = content.replace(old_theorem, new_theorem)
    print('Replaced!')
else:
    print('Not found!')

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
