f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 当前顺序：correlation(def) -> transferOperator(opaque) -> correlation_transfer_operator_identity(theorem)
# 需要改为：transferOperator(opaque) -> correlation(def) -> correlation_transfer_operator_identity(theorem)

old_block = """/-- 测地流关联函数（定义）：
    C(f,g,t) = transferOperator t f g，即转移算子的矩阵元（减去平衡态贡献）。
    具体实现需要 L²(M) 与 Liouville 测度，当前通过 transferOperator 抽象。 -/
def correlation (f g : ℝ → ℂ) (t : ℝ) : ℂ := transferOperator t f g

/-- 测地流转移算子（opaque）：
    L_t: L²(M) → L²(M)，由测地流 φ_t 诱导的 Perron-Frobenius 转移算子。
    对观测函数 f，(L_t f)(x) = f(φ_t x)（或其加权版本）。
    转移算子是动力系统谱理论的核心对象：
    关联函数 C(f,g,t) = ⟨g, L_t f⟩ - ⟨g,1⟩⟨1,f⟩ 是 L_t 的矩阵元。
    Dolgopyat 定理的核心是证明 L_t 在不稳定方向上有谱隙。
    当前用 opaque 抽象，具体实现需要 L²(M) 与 Liouville 测度。 -/
opaque transferOperator : ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ"""

new_block = """/-- 测地流转移算子（opaque）：
    L_t: L²(M) → L²(M)，由测地流 φ_t 诱导的 Perron-Frobenius 转移算子。
    对观测函数 f，(L_t f)(x) = f(φ_t x)（或其加权版本）。
    转移算子是动力系统谱理论的核心对象：
    关联函数 C(f,g,t) = ⟨g, L_t f⟩ - ⟨g,1⟩⟨1,f⟩ 是 L_t 的矩阵元。
    Dolgopyat 定理的核心是证明 L_t 在不稳定方向上有谱隙。
    当前用 opaque 抽象，具体实现需要 L²(M) 与 Liouville 测度。 -/
opaque transferOperator : ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ

/-- 测地流关联函数（定义）：
    C(f,g,t) = transferOperator t f g，即转移算子的矩阵元（减去平衡态贡献）。
    具体实现需要 L²(M) 与 Liouville 测度，当前通过 transferOperator 抽象。 -/
def correlation (f g : ℝ → ℂ) (t : ℝ) : ℂ := transferOperator t f g"""

content = content.replace(old_block, new_block, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: swapped correlation and transferOperator')
