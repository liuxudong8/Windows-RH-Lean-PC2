import sys
path = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

start_marker = '/-- ζ 非平凡零点的加权级数收敛性（公理'
end_marker = '    Summable (fun (n : ℕ) => (zeroMultiplicity (nontrivialZeroEnum n) : ℝ) / (1 + |(nontrivialZeroEnum n).im|) ^ 2)'

start_idx = content.find(start_marker)
end_idx = content.find(end_marker, start_idx) + len(end_marker)

theorem_block = open(r'C:\proj2\theorem_block.txt', 'r', encoding='utf-8').read()

content = content[:start_idx] + theorem_block + content[end_idx:]
with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Wrote theorem')
