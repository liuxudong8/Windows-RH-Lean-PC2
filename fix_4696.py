import io

f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with io.open(f, 'r', encoding='utf-8') as fh:
    c = fh.read()

old = "      _ ≤ 1/(‖s‖ * ‖s + 1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by admit"
new = "      _ ≤ 1/(‖s‖ * ‖s + 1‖) * ∫ x in Set.Icc ε₀ R₀, ‖(deriv (deriv h.toFun)) x‖ * x^(s.re + 1) := by exact?"

assert old in c, "old not found"
c = c.replace(old, new)

with io.open(f, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write(c)
print("done")
