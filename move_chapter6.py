f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    lines = fh.readlines()

# 找到第6章开始（/- 6. 显式积分核基础设施）
chapter6_start = None
for i, line in enumerate(lines):
    if '/- 6. 显式积分核基础设施' in line:
        chapter6_start = i
        break

# 第6章到文件结束
chapter6_end = len(lines)
print(f'Chapter 6: lines {chapter6_start+1} to {chapter6_end}')

# 提取第6章内容
chapter6 = lines[chapter6_start:chapter6_end]

# 删除第6章原位置
del lines[chapter6_start:chapter6_end]

# 找到 fLaplacianKernel 的位置（在新的行号中）
fkl_idx = None
for i, line in enumerate(lines):
    if 'opaque fLaplacianKernel : TestFunction' in line:
        fkl_idx = i
        break
print(f'fLaplacianKernel at line {fkl_idx+1}')

# 找到 fLaplacianKernel 注释开始
fkl_comment_start = None
for i in range(fkl_idx, max(0, fkl_idx-10), -1):
    if '/--' in lines[i]:
        fkl_comment_start = i
        break

# 在 fLaplacianKernel 注释之前插入第6章基础设施
# 但需要先从 chapter6 中删除两个要删除的公理
chapter6_text = ''.join(chapter6)

# 删除 geometricKernelTrace_integral_representation 公理
import re
chapter6_text = re.sub(
    r'/-- 几何侧迹的积分核表示（公理，精确版）：.*?axiom geometricKernelTrace_integral_representation.*?\n\n',
    '',
    chapter6_text,
    flags=re.DOTALL
)

# 删除 fLaplacianKernel_heatKernel_exact 公理
chapter6_text = re.sub(
    r'/-- f\(Δ\) 积分核的热核表示（精确版，公理）：.*?axiom fLaplacianKernel_heatKernel_exact.*?\n\n',
    '',
    chapter6_text,
    flags=re.DOTALL
)

# 在 fLaplacianKernel 注释之前插入
lines[fkl_comment_start:fkl_comment_start] = [chapter6_text + '\n']

# 重新计算 fLaplacianKernel 位置
fkl_idx = None
for i, line in enumerate(lines):
    if 'opaque fLaplacianKernel : TestFunction' in line:
        fkl_idx = i
        break

# 把 fLaplacianKernel 从 opaque 改为 def
# 先找到注释开始
fkl_comment_start = None
for i in range(fkl_idx, max(0, fkl_idx-10), -1):
    if '/--' in lines[i]:
        fkl_comment_start = i
        break

# 替换注释和定义
new_fkl_comment = '''/-- f(Δ) 的积分核（定义）：K_f(z, w) = ∫₀^∞ L[f](t) · K_t(z,w) dt。
    即 f(Δ) 的积分核是热核的 Laplace 变换加权积分。
    推导：由谱定理 f(Δ) = ∫ f(λ) dE(λ)，热核 e^{-tΔ} = ∫ e^{-tλ} dE(λ)，
    由 Laplace 反演得 K_f = ∫ L[f](t) K_t dt。 -/
'''
new_fkl_def = 'def fLaplacianKernel (f : TestFunction) (z w : ManifoldM) : ℂ :=\n    realIntegral (fun t => laplaceTransform f t * heatKernel t z w)\n'

lines[fkl_comment_start:fkl_idx+1] = [new_fkl_comment, new_fkl_def]

# 找到 geometricKernelTrace 位置
gkt_idx = None
for i, line in enumerate(lines):
    if 'opaque geometricKernelTrace : TestFunction → ℂ' in line:
        gkt_idx = i
        break

# 找到注释开始
gkt_comment_start = None
for i in range(gkt_idx, max(0, gkt_idx-15), -1):
    if '/--' in lines[i]:
        gkt_comment_start = i
        break

# 替换注释和定义
new_gkt_comment = '''/-- 几何侧迹（定义，热核积分形式）：
    Tr_geo(f) = ∫_M Σ_{γ∈Γ} K_f(z, γz) dz
    即 geometricKernelTrace f = manifoldIntegral (fun z => gammaPeriodization (fLaplacianKernel f) z z)。
    这是 Arthur 迹公式几何侧的显式积分表达式。 -/
'''
new_gkt_def = 'def geometricKernelTrace (f : TestFunction) : ℂ :=\n    manifoldIntegral (fun z => gammaPeriodization (fLaplacianKernel f) z z)\n'

lines[gkt_comment_start:gkt_idx+1] = [new_gkt_comment, new_gkt_def]

with open(f, 'w', encoding='utf-8') as fh:
    fh.writelines(lines)
print('Done: moved chapter 6, changed fLaplacianKernel and geometricKernelTrace to def')
