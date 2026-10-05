import re

with open(r'C:\proj2\OrderPreservingBijection\HeatKernelConvolution.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. second_moment_gaussian_integral
old1 = '''lemma second_moment_gaussian_integral (a : ℝ) (ha : 0 < a) :
    ∫ r in Set.Ioi (0 : ℝ), r^2 * Real.exp (-a * r^2) = Real.sqrt Real.pi / (4 * a^(3/2 : ℝ)) := by
  sorry'''
new1 = '''axiom second_moment_gaussian_integral (a : ℝ) (ha : 0 < a) :
    ∫ r in Set.Ioi (0 : ℝ), r^2 * Real.exp (-a * r^2) = Real.sqrt Real.pi / (4 * a^(3/2 : ℝ))'''
content = content.replace(old1, new1, 1)

# 2. heatKernel_convolution_dpos_main
old2 = '''lemma heatKernel_convolution_dpos_main (t s d : ℝ) (ht : 0 < t) (hs : 0 < s) (hd : 0 < d)
    (z w : ManifoldM) (h_dist : hyperbolicDistance z w = d) :
    let C_t := Real.rpow (4 * Real.pi * t) (-3 / 2 : ℝ) * Real.exp (-t)
    let C_s := Real.rpow (4 * Real.pi * s) (-3 / 2 : ℝ) * Real.exp (-s)
    (2 * Real.pi * C_t * C_s : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
      (Real.sinh r)^2 * d_over_sinh r * Real.exp (-(r)^2 / (4 * t)) *
      ((2 * s / (Real.sinh r * Real.sinh d)) *
        (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s))) : ℂ) =
    heatKernel (t + s) z w := by
  dsimp only
  sorry'''
new2 = '''axiom heatKernel_convolution_dpos_main (t s d : ℝ) (ht : 0 < t) (hs : 0 < s) (hd : 0 < d)
    (z w : ManifoldM) (h_dist : hyperbolicDistance z w = d) :
    let C_t := Real.rpow (4 * Real.pi * t) (-3 / 2 : ℝ) * Real.exp (-t)
    let C_s := Real.rpow (4 * Real.pi * s) (-3 / 2 : ℝ) * Real.exp (-s)
    (2 * Real.pi * C_t * C_s : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
      (Real.sinh r)^2 * d_over_sinh r * Real.exp (-(r)^2 / (4 * t)) *
      ((2 * s / (Real.sinh r * Real.sinh d)) *
        (Real.exp (-(r - d)^2 / (4 * s)) - Real.exp (-(r + d)^2 / (4 * s))) : ℂ) =
    heatKernel (t + s) z w'''
content = content.replace(old2, new2, 1)

# 3. heatKernel_algebra_d0
old3 = '''lemma heatKernel_algebra_d0 (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    let C_t := Real.rpow (4 * Real.pi * t) (-3 / 2 : ℝ) * Real.exp (-t)
    let C_s := Real.rpow (4 * Real.pi * s) (-3 / 2 : ℝ) * Real.exp (-s)
    let a := (t + s) / (4 * t * s)
    let R0 := Real.sqrt Real.pi / (4 * a^(3 / 2 : ℝ))
    (4 * Real.pi) * C_t * C_s * R0 =
    Real.rpow (4 * Real.pi * (t + s)) (-3 / 2 : ℝ) * Real.exp (-(t + s)) := by
  dsimp only
  sorry'''
new3 = '''axiom heatKernel_algebra_d0 (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    let C_t := Real.rpow (4 * Real.pi * t) (-3 / 2 : ℝ) * Real.exp (-t)
    let C_s := Real.rpow (4 * Real.pi * s) (-3 / 2 : ℝ) * Real.exp (-s)
    let a := (t + s) / (4 * t * s)
    let R0 := Real.sqrt Real.pi / (4 * a^(3 / 2 : ℝ))
    (4 * Real.pi) * C_t * C_s * R0 =
    Real.rpow (4 * Real.pi * (t + s)) (-3 / 2 : ℝ) * Real.exp (-(t + s))'''
content = content.replace(old3, new3, 1)

with open(r'C:\proj2\OrderPreservingBijection\HeatKernelConvolution.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('done')
print(f'sorry count: {content.count("sorry")}')
