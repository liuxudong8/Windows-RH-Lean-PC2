import Mathlib

example {a b c : ℝ} (h1 : a < b) (h2 : b < 1 - c) (h3 : c = 1 / 2) : a + c < 1 := by linarith

example {a b c : ℝ} (h1 : a < b) (h2 : b < 1 - c) (h3 : c = 1 / 2) : a + c < 1 := by nlinarith [h1, h2, h3]