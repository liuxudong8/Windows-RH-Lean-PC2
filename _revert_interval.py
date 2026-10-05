from pathlib import Path
p = Path(r"c:\proj2\OrderPreservingBijection\Interpolation.lean")
t = p.read_text(encoding="utf-8")
start = t.index("lemma intervalIndicator_mellinTransform")
end = t.index("/-- exp(z) = 1")
new = """lemma intervalIndicator_mellinTransform (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) (hs : s ≠ 0) :
    melinTransform (intervalIndicator a b ha hab) s =
    (Complex.exp (s * (Real.log b : ℂ)) - Complex.exp (s * (Real.log a : ℂ))) / s := by sorry

"""
t = t[:start] + new + t[end:]
p.write_text(t, encoding="utf-8")
print("reverted")
