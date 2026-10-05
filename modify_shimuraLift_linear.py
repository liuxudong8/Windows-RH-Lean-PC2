#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# 读取文件
file_path = r"C:\proj2\OrderPreservingBijection\stage_4.lean"

with open(file_path, 'r', encoding='utf-8') as f:
    content = f.read()

# 旧的证明
old = """theorem shimuraLift_linear (a : ℂ) (f : L2ManifoldX) :
    shimuraLift (a • f) = a • shimuraLift f := by sorry"""

# 新的证明
new = """-- 测试 L2Function 的外延性定理
lemma l2function_ext {M : Type} [MeasurableSpace M] {μ : MeasureTheory.Measure M}
    (f g : L2Function M μ) (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  congr
  <;> exact h

-- 测试 shimuraLift_linear 的 toFun 相等
lemma shimuraLift_linear_toFun (a : ℂ) (f : L2ManifoldX) (z : ManifoldM) :
    (shimuraLift (a • f)).toFun z = (a • shimuraLift f).toFun z := by
  have h1 : (shimuraLift (a • f)).toFun z =
      manifoldIntegralX (fun w : ManifoldX => shimuraKernel z w * (a • f) w) := by rfl
  have h2 : (a • shimuraLift f).toFun z =
      a * (shimuraLift f).toFun z := by rfl
  rw [h1, h2]
  have h3 : (fun w : ManifoldX => shimuraKernel z w * (a • f) w) =
      fun w : ManifoldX => a * (shimuraKernel z w * f w) := by
    funext w
    have h4 : (a • f) w = a * f w := by rfl
    rw [h4]
    <;> ring
  rw [h3]
  have h5 : (shimuraLift f).toFun z =
      manifoldIntegralX (fun w : ManifoldX => shimuraKernel z w * f w) := by rfl
  rw [h5]
  -- 现在我们需要证明：
  -- manifoldIntegralX (fun w => a * (shimuraKernel z w * f w)) =
  -- a * manifoldIntegralX (fun w => shimuraKernel z w * f w)
  -- 这就是积分的线性性！
  have h_int : MeasureTheory.Integrable (fun w : ManifoldX => shimuraKernel z w * f w) hyperbolicMeasure2 :=
    shimura_kernel_integrand_integrable z f
  exact MeasureTheory.integral_smul a (fun w => shimuraKernel z w * f w)

-- 现在我们已经证明了 toFun 相等，接下来我们需要证明两个 L2Function 相等
theorem shimuraLift_linear (a : ℂ) (f : L2ManifoldX) :
    shimuraLift (a • f) = a • shimuraLift f := by
  have h_toFun : (shimuraLift (a • f)).toFun = (a • shimuraLift f).toFun := by
    funext z
    exact shimuraLift_linear_toFun a f z
  exact l2function_ext (shimuraLift (a • f)) (a • shimuraLift f) h_toFun"""

# 替换
content = content.replace(old, new)

# 写回文件
with open(file_path, 'w', encoding='utf-8') as f:
    f.write(content)

print("Modified!")
