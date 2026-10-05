path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Fix 1: h_compact in whitney - separate have and exact
content = content.replace(
    "  have h_compact : \u2203 (R' : \u211d), 0 < R' \u2227 \u2200 (x : \u211d), |x| > R' \u2192 f0_fun x = 0 := by\n    refine \u27e8R, ?_, ?_\u27e9\n    \u00b7 have h1 : 0 < \u039b1 := by linarith; exact lt_max_of_lt_left h1\n    \u00b7 intro x hx",
    "  have hR_pos : 0 < R := by\n    have h1 : 0 < \u039b1 := by linarith\n    exact lt_max_of_lt_left h1\n  have hR_main : \u2200 (x : \u211d), |x| > R \u2192 f0_fun x = 0 := by\n    intro x hx"
)

# Need to close the have and add exact
content = content.replace(
    "        simp only [f0_fun]; rw [if_pos h_le]\n  let f0 : TestFunction",
    "        simp only [f0_fun]; rw [if_pos h_le]\n  have h_compact : \u2203 (R' : \u211d), 0 < R' \u2227 \u2200 (x : \u211d), |x| > R' \u2192 f0_fun x = 0 :=\n    \u27e8R, hR_pos, hR_main\u27e9\n  let f0 : TestFunction"
)

# Fix 2: h_one - separate have and rw
content = content.replace(
    "  have h_one : \u2200 x, \u039b0 \u2264 x \u2227 x \u2264 \u039b1 \u2192 f0.eval x = 1 := by\n    intro x hx; simp only [f0, TestFunction.eval, f0_fun]\n    have h1 : \u00ac(x \u2264 \u039b0 / 2) := by linarith; rw [if_neg h1, if_pos hx]",
    "  have h_one : \u2200 x, \u039b0 \u2264 x \u2227 x \u2264 \u039b1 \u2192 f0.eval x = 1 := by\n    intro x hx; simp only [f0, TestFunction.eval, f0_fun]\n    have h1 : \u00ac(x \u2264 \u039b0 / 2) := by linarith\n    rw [if_neg h1, if_pos hx]"
)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed whitney h_compact and h_one')
