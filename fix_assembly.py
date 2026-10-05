# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到组装部分并替换
for i, line in enumerate(lines):
    if 'rw [h_main1, h_main2]' in line:
        # 替换接下来的行
        new_lines = [
            '  rw [h_main1, h_main2]\n',
            '  have h_final1 : contourIntegral (fun s => (∑\' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * (principalIdealNorm γ.element : ℂ)^(-s)) * melinTransform f.toTestFunction s) =\n',
            '      contourIntegral (fun s => primeDirichletSeries s * melinTransform f.toTestFunction s) := by\n',
            '    apply contourIntegral_congr\n',
            '    intro s\n',
            '    rw [h_dirichlet_eq s]\n',
            '  exact h_final1\n'
        ]
        # 替换从 i 开始的 5 行
        lines[i:i+5] = new_lines
        print(f'Replaced lines {i+1} to {i+len(new_lines)}')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
