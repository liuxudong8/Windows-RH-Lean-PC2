import OrderPreservingBijection.stage_4

open OrderPreservingBijection
open Complex

namespace RHSpectralDuality

-- 测试：指数函数线性无关
-- 目标：若 λ_j 互不相同，则 {e^{λ_j u}} 线性无关

#check Function.Injective

-- 测试复数幂
#check (fun (x : ℝ) (z : ℂ) => (x : ℂ) ^ z)

-- 测试 Matrix
#check Matrix

end RHSpectralDuality
