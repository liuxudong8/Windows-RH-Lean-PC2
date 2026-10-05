f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    lines = fh.readlines()

# 删除从 "单个谱点约束的 Mellin 叠加" 注释开始到 spectral_preserving_melin_superposition_from 证明结束
start_idx = None
end_idx = None
for i, line in enumerate(lines):
    if '单个谱点约束的 Mellin 叠加' in line and start_idx is None:
        start_idx = i
    if 'spectral_preserving_superposition_from_any_base f g' in line:
        end_idx = i + 1  # 包含这行
        break

print(f"Deleting lines {start_idx+1} to {end_idx+1}")
print(f"Start: {lines[start_idx].strip()[:60]}")
print(f"End: {lines[end_idx].strip()[:60]}")

# 删除 start_idx 到 end_idx（含），以及后面的空行
while end_idx + 1 < len(lines) and lines[end_idx + 1].strip() == '':
    end_idx += 1

del lines[start_idx:end_idx+1]

with open(f, 'w', encoding='utf-8') as fh:
    fh.writelines(lines)
print(f"Deleted {end_idx - start_idx + 1} lines")
