path = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

start = content.find('/-- ζ 非平凡零点的加权级数收敛性（公理')
end_marker = '    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2)'
end_idx = content.find(end_marker, start) + len(end_marker)

theorem_block = open(r'C:\proj2\theorem_block_v2.txt', 'r', encoding='utf-8').read()

content = content[:start] + theorem_block + content[end_idx:]
with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Applied theorem v2')
