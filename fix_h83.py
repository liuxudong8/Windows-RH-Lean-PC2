# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 h83 的位置
h83_line = None
for i in range(len(lines)):
    if 'have h83 :' in lines[i] and i > 4570 and i < 4580:
        h83_line = i
        print(f"Found h83 at line {i+1}")
        break

if h83_line is not None:
    # 替换 h83 的证明
    new_h83 = "    have h83 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = B' * (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by\n"
    new_h83 += "      -- 步骤1：集合积分转区间积分\n"
    new_h83 += "      have h1 : ∫ x in Set.Icc ε₀ R₀, B' * x^(s.re + 1) = ∫ x in ε₀..R₀, B' * x^(s.re + 1) := by\n"
    new_h83 += "        rw [MeasureTheory.setIntegral_Icc]\n"
    new_h83 += "        <;> linarith\n"
    new_h83 += "      -- 步骤2：提取常数 B'\n"
    new_h83 += "      have h2 : ∫ x in ε₀..R₀, B' * x^(s.re + 1) = B' * ∫ x in ε₀..R₀, x^(s.re + 1) := by\n"
    new_h83 += "        rw [intervalIntegral.const_mul]\n"
    new_h83 += "      -- 步骤3：应用幂函数积分公式\n"
    new_h83 += "      have h3 : ∫ x in ε₀..R₀, x^(s.re + 1) = (R₀^(s.re + 2) - ε₀^(s.re + 2)) / (s.re + 2) := by\n"
    new_h83 += "        rw [intervalIntegral.integral_rpow hε₀_pos hε₀_lt_R₀]\n"
    new_h83 += "        <;> field_simp\n"
    new_h83 += "        <;> ring_nf\n"
    new_h83 += "      -- 步骤4：串联所有等式\n"
    new_h83 += "      rw [h1, h2, h3]\n"
    new_h83 += "      <;> ring\n"
    
    # 替换 h83 那一行（包括后面的 admit）
    lines[h83_line] = new_h83
    # 删除后面的 admit 行（如果有的话）
    if h83_line + 1 < len(lines) and 'admit' in lines[h83_line + 1]:
        del lines[h83_line + 1]

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
