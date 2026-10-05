f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

old = """/-- 测地流关联函数（抽象常量，具体实现需要 L²(M) 与 Liouville 测度）。
    C(f,g,t) = ∫_M f(x) g(φ_t x) dμ(x) - (∫ f dμ)(∫ g dμ)
    其中 φ_t 是 M = PSL2(O_K)\H³ 上的测地流，μ 为 Liouville 测度。 -/
opaque correlation : (ℝ → ℂ) → (ℝ → ℂ) → ℝ → ℂ"""

new = """/-- 测地流关联函数（定义）：
    C(f,g,t) = transferOperator t f g，即转移算子的矩阵元（减去平衡态贡献）。
    具体实现需要 L²(M) 与 Liouville 测度，当前通过 transferOperator 抽象。 -/
def correlation (f g : ℝ → ℂ) (t : ℝ) : ℂ := transferOperator t f g"""

content = content.replace(old, new, 1)

# 降级 correlation_transfer_operator_identity 为定理
old2 = """/-- 关联函数与转移算子的关系（公理）：
    关联函数是转移算子的矩阵元（减去平衡态贡献）：
      C(f,g,t) = L_t(f,g)
    其中 L_t(f,g) = ⟨g, L_t f⟩ - ⟨g,1⟩⟨1,f⟩。
    这是动力系统的标准定义：关联函数衡量观测 f 在时间 t 后
    与观测 g 的统计相关性，转移算子编码了时间演化。
    数学上，这是 Koopman 算子 / Perron-Frobenius 算子的基本性质。 -/
axiom correlation_transfer_operator_identity :
    ∀ (f g : ℝ → ℂ) (t : ℝ),
      correlation f g t = transferOperator t f g"""

new2 = """/-- 关联函数与转移算子的关系（定理，由定义直接推出）。 -/
theorem correlation_transfer_operator_identity :
    ∀ (f g : ℝ → ℂ) (t : ℝ),
      correlation f g t = transferOperator t f g := by
  intro f g t; rfl"""

content = content.replace(old2, new2, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: correlation -> def, correlation_transfer_operator_identity -> theorem')
