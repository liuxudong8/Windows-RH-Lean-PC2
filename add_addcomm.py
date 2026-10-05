path = r'C:\proj2\OrderPreservingBijection\BasicInfrastructure.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Add Zero and AddCommMonoid after SMul instance
smul_end = """      intro x hx
      have hf : f.eval x = 0 := hR.2 x hx
      rw [hf] <;> ring"""

new_instances = """      intro x hx
      have hf : f.eval x = 0 := hR.2 x hx
      rw [hf] <;> ring

/-- TestFunction 的零元素：恒为零的函数。 -/
noncomputable instance : Zero TestFunction where
  zero :=
    { toFun := fun _ => (0 : ℂ)
      hasCompactSupport := ⟨1, by norm_num, fun x _ => rfl⟩ }

/-- TestFunction 的 AddCommMonoid 实例：逐点加法，零元为恒零函数。 -/
noncomputable instance : AddCommMonoid TestFunction where
  add := (· + ·)
  zero := 0
  add_assoc := by
    intro a b c
    apply TestFunction.mk.injEq
    funext x
    simp [TestFunction.eval] <;> ring
  zero_add := by
    intro a
    apply TestFunction.mk.injEq
    funext x
    simp [TestFunction.eval] <;> ring
  add_zero := by
    intro a
    apply TestFunction.mk.injEq
    funext x
    simp [TestFunction.eval] <;> ring
  add_comm := by
    intro a b
    apply TestFunction.mk.injEq
    funext x
    simp [TestFunction.eval] <;> ring"""

content = content.replace(smul_end, new_instances)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Added Zero and AddCommMonoid instances')
