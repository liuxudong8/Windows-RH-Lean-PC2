# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 sorry 行并替换
for i, line in enumerate(lines):
    if i == 1413 and line.strip() == 'sorry':
        # 替换为证明框架
        new_lines = [
            '  -- 步骤 1：Mellin 反演公式\n',
            '  have h_mellin_inversion : ∀ (γ : PrimeGeodesic),\n',
            '      f.toTestFunction.eval (geodesicLengthPrime γ) =\n',
            '        contourIntegral (fun s => melinTransform f.toTestFunction s * (principalIdealNorm γ.element : ℂ)^(-s)) := by\n',
            '    intro γ\n',
            '    sorry\n',
            '  -- 步骤 2：代入几何侧求和\n',
            '  have h_main1 : ∑\' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * f.toTestFunction.eval (geodesicLengthPrime γ) =\n',
            '      ∑\' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * contourIntegral (fun s => melinTransform f.toTestFunction s * (principalIdealNorm γ.element : ℂ)^(-s)) := by\n',
            '    apply tsum_congr\n',
            '    intro γ\n',
            '    rw [h_mellin_inversion γ]\n',
            '  -- 步骤 3：求和-积分交换\n',
            '  have h_main2 : ∑\' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * contourIntegral (fun s => melinTransform f.toTestFunction s * (principalIdealNorm γ.element : ℂ)^(-s)) =\n',
            '      contourIntegral (fun s => (∑\' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * (principalIdealNorm γ.element : ℂ)^(-s)) * melinTransform f.toTestFunction s) := by\n',
            '    sorry\n',
            '  -- 步骤 4：证明 Dirichlet 级数相等\n',
            '  have h_dirichlet_eq : ∀ (s : ℂ),\n',
            '      (∑\' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * (principalIdealNorm γ.element : ℂ)^(-s)) = primeDirichletSeries s := by\n',
            '    intro s\n',
            '    sorry\n',
            '  -- 组装\n',
            '  rw [h_main1, h_main2]\n',
            '  have h_final : contourIntegral (fun s => (∑\' (γ : PrimeGeodesic), (orbitWeight γ : ℂ) * (principalIdealNorm γ.element : ℂ)^(-s)) * melinTransform f.toTestFunction s) =\n',
            '      contourIntegral (fun s => primeDirichletSeries s * melinTransform f.toTestFunction s) := by\n',
            '    apply congr_arg contourIntegral\n',
            '    funext s\n',
            '    rw [h_dirichlet_eq s]\n',
            '  exact h_final\n'
        ]
        # 替换从 i 开始的 1 行
        lines[i:i+1] = new_lines
        print(f'Replaced line {i+1} with {len(new_lines)} lines')
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
