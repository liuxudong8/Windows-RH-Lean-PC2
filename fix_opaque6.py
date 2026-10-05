f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 在 manifoldIntegral 之后引入 manifoldIntegralX
old_mint = """opaque manifoldIntegral : (ManifoldM → ℂ) → ℂ"""

new_mint = """opaque manifoldIntegral : (ManifoldM → ℂ) → ℂ

/-- 二维双曲曲面 X 上的积分（opaque）：∫_X h(w) dw。
    与 manifoldIntegral 类似，但定义域是 ManifoldX 而非 ManifoldM。
    用于 Shimura 提升算子的积分定义。 -/
opaque manifoldIntegralX : (ManifoldX → ℂ) → ℂ"""

content = content.replace(old_mint, new_mint, 1)

# 2. 删除 integralOperator opaque，改为注释
old_iop = """/-- 积分算子（opaque，类型化）：给定核 K : M → X → ℂ，
    定义 (T_K f)(z) = ∫_X K(z,w) f(w) dw，类型为 L²(X) → L²(M)。
    类型参数保证核的源空间和目标空间与算子的定义域/值域一致。 -/
opaque integralOperator {M X : Type} : (M → X → ℂ) → L2Function X → L2Function M

"""

new_iop = ""

content = content.replace(old_iop, new_iop, 1)

# 3. 重写 shimuraLift
old_sl = """/-- Shimura 提升算子（定义，类型化）：U : L²(X) → L²(M) = integralOperator shimuraKernel。
    类型安全：只接受二维 L² 函数，输出三维 L² 函数。 -/
def shimuraLift : L2Function ManifoldX → L2Function ManifoldM :=
    integralOperator shimuraKernel"""

new_sl = """/-- Shimura 提升算子（定义，类型化）：U : L²(X) → L²(M)。
    (U f)(z) = ∫_X Θ(z,w) f(w) dw，其中 Θ = shimuraKernel。
    类型安全：只接受二维 L² 函数，输出三维 L² 函数。 -/
def shimuraLift (f : L2Function ManifoldX) : L2Function ManifoldM :=
    fun (z : ManifoldM) => manifoldIntegralX (fun (w : ManifoldX) => shimuraKernel z w * f w)"""

content = content.replace(old_sl, new_sl, 1)

# 4. 重写 heatOperator
old_ho = """noncomputable def heatOperator (t : ℝ) : L2Function ManifoldM → L2Function ManifoldM :=
    integralOperator (fun z w => heatKernel t z w)"""

new_ho = """noncomputable def heatOperator (t : ℝ) (f : L2Function ManifoldM) : L2Function ManifoldM :=
    fun (z : ManifoldM) => manifoldIntegral (fun (w : ManifoldM) => heatKernel t z w * f w)"""

content = content.replace(old_ho, new_ho, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: integralOperator inlined, manifoldIntegralX introduced')
