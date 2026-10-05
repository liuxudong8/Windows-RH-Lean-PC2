path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

old = """  intro s hs
  have h1 : melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s := by
    rw [h_melin_eq]
  rw [h1]
  have h2 : melinTransform h s = u s := hh s hs
  rw [h2]
  simp only [u] <;> abel"""

new = """  intro s hs
  have h1 : melinTransform f.toTestFunction s = melinTransform f0.toTestFunction s + melinTransform h s := by
    have h_eq := congrFun h_melin_eq s
    exact h_eq
  rw [h1]
  have h2 : melinTransform h s = u s := hh s hs
  rw [h2]
  simp only [u] <;> ring"""

content = content.replace(old, new)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed congrFun')
