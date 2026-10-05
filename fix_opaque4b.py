f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 删除旧注释块
old_comment = """/-- 三维双曲空间热核的显式公式（公理）：
    K_t(z,w) = (4πt)^(-3/2) · e^{-t} · e^{-d(z,w)²/(4t)} · (d(z,w)/sinh(d(z,w)))
    其中 d(z,w) 是双曲距离。
    这是三维双曲空间 H³ 上热方程的基本解，由 McKean (1972) 给出。
    推导：三维双曲空间的径向热核满足
      ∂_t u = ∂_r² u + 2 coth(r) ∂_r u - u
    其解为上述显式公式。
    因子 d/sinh(d) 来自三维双曲空间的体积元 r² sinh²(r) dr。
    对 t>0，此公式给出光滑、正定、对称的热核。 -/
/-- 热核显式公式（定理，由定义直接推出）。 -/"""

new_comment = """/-- 热核显式公式（定理，由定义直接推出）。 -/"""

content = content.replace(old_comment, new_comment, 1)

# 2. 修复证明
old_proof = """  rw [heatKernel]; rw [if_pos ht]; rfl"""

new_proof = """  simp [heatKernel, ht]"""

content = content.replace(old_proof, new_proof, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: fixed comment and proof')
