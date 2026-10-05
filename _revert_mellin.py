from pathlib import Path
p = Path(r"c:\proj2\OrderPreservingBijection\MellinInfrastructure.lean")
t = p.read_text(encoding="utf-8")
start = t.index("lemma mellin_integrand_integrable")
end = t.index("/-- Mellin 变换的线性性")
new = """lemma mellin_integrand_integrable (f : TestFunction) (s : ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by sorry

"""
t = t[:start] + new + t[end:]
p.write_text(t, encoding="utf-8")
print("reverted")
