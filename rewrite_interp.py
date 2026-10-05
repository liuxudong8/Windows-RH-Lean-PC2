path = r'C:\proj2\OrderPreservingBijection\Interpolation.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# 1. Replace mellin_transform_countable_surjectivity axiom with finite-set version theorem
old_axiom = """/-- Mellin 变换的可数集满射性（公理，纯 Paley-Wiener 定理）：
    对任意可数点集 T ⊆ ℂ 和任意赋值 w : ℂ → ℂ，存在紧支集 TestFunction f
    使得 Mellin 变换 M[f] 在 T 上等于 w。
    这是 Paley-Wiener 定理的直接推论：紧支集函数的 Mellin 变换是整函数，
    且在可数点集上可任意指定取值（函数空间无限维）。
    不涉及点插值约束，是纯分析断言。 -/
axiom mellin_transform_countable_surjectivity
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (h : TestFunction), ∀ (s : ℂ), s ∈ T → melinTransform h s = w s"""

new_axiom = """/-- Mellin 变换的有限集满射性（定理，由区间指示函数基 + 有限维线性代数推出）：
    对任意有限点集 T ⊆ ℂ 和任意赋值 w : ℂ → ℂ，存在紧支集 TestFunction f
    使得 Mellin 变换 M[f] 在 T 上等于 w。
    证明：将 T 枚举为 t : Fin m → ℂ，由 mellin_finite_surjectivity 直接得到。
    注意：可数集版本在数学上不成立（指数型整函数零点密度限制），
    反证法中只需要有限集版本。 -/
theorem mellin_finite_set_surjectivity
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (h : TestFunction), ∀ (s : ℂ), s ∈ T → melinTransform h s = w s := by
  let s : Finset ℂ := hT.toFinset
  have hTs : (↑s : Set ℂ) = T := hT.coe_toFinset
  let m := s.card
  let t : Fin m → ℂ := fun i => s.orderEmbOfFin i
  have ht_inj : Function.Injective t := by
    intro i j h
    exact Finset.orderEmbOfFin_inj.mp h
  have h_range : Set.range t = T := by
    rw [←hTs]
    exact Finset.range_orderEmbOfFin s
  let w' : Fin m → ℂ := fun i => w (t i)
  rcases mellin_finite_surjectivity t ht_inj w' with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  intro s hs
  have h_in_range : s ∈ Set.range t := by rw [h_range]; exact hs
  rcases h_in_range with ⟨i, rfl⟩
  exact hh i"""

content = content.replace(old_axiom, new_axiom)

# 2. Modify mellin_surjectivity_over_point_fiber: T.Countable -> T.Finite, use mellin_finite_set_surjectivity
old_fiber = """theorem mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s) := by
  let u : ℂ → ℂ := fun s => w s - melinTransform f0.toTestFunction s
  rcases mellin_transform_countable_surjectivity T hT u with ⟨h, hh⟩"""

new_fiber = """theorem mellin_surjectivity_over_point_fiber
    (f0 : MollifiedTestFunction) (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction),
      (∀ (x : ℝ), x ∈ S → f.toTestFunction.eval x = f0.toTestFunction.eval x) ∧
      (∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s) := by
  let u : ℂ → ℂ := fun s => w s - melinTransform f0.toTestFunction s
  rcases mellin_finite_set_surjectivity T hT u with ⟨h, hh⟩"""

content = content.replace(old_fiber, new_fiber)

# 3. Modify paley_wiener_whitney_joint_interpolation: hT.Countable -> hT.Finite
old_pww = """theorem paley_wiener_whitney_joint_interpolation
    (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (v : ℝ → ℂ) (h_vfin : Set.Finite {x ∈ S | v x ≠ 0})
    (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :"""

new_pww = """theorem paley_wiener_whitney_joint_interpolation
    (S : Set ℝ) (hS : S.Countable) (h_sep : PointSetSeparable S)
    (v : ℝ → ℂ) (h_vfin : Set.Finite {x ∈ S | v x ≠ 0})
    (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :"""

content = content.replace(old_pww, new_pww)

# 4. Replace mellin_countable_interpolation with mellin_finite_interpolation
old_countable = """/-- 可数集上 Mellin 变换任意赋值（定理）： -/
theorem mellin_countable_interpolation (T : Set ℂ) (hT : T.Countable) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction), ∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s := by
  have h_sep_empty : PointSetSeparable (∅ : Set ℝ) := by
    refine ⟨1, 2, by norm_num, by norm_num, ?_, ?_⟩
    · intro x hx; simp at hx
    · intro x hx; simp at hx
  have h_vfin_empty : Set.Finite {x ∈ (∅ : Set ℝ) | (fun _ : ℝ => (0 : ℂ)) x ≠ 0} := by simp
  rcases paley_wiener_whitney_joint_interpolation (∅ : Set ℝ) Set.countable_empty h_sep_empty (fun _ => 0) h_vfin_empty T hT w with ⟨f, _, h_melin⟩
  exact ⟨f, h_melin⟩"""

new_finite = """/-- 有限集上 Mellin 变换任意赋值（定理，由有限集满射性 + 纤维丰富性推出）：
    对任意有限点集 T ⊆ ℂ 和任意赋值 w，存在磨光函数 f 使得 M[f]|_T = w。 -/
theorem mellin_finite_interpolation (T : Set ℂ) (hT : T.Finite) (w : ℂ → ℂ) :
    ∃ (f : MollifiedTestFunction), ∀ (s : ℂ), s ∈ T → melinTransform f.toTestFunction s = w s := by
  have h_sep_empty : PointSetSeparable (∅ : Set ℝ) := by
    refine ⟨1, 2, by norm_num, by norm_num, ?_, ?_⟩
    · intro x hx; simp at hx
    · intro x hx; simp at hx
  have h_vfin_empty : Set.Finite {x ∈ (∅ : Set ℝ) | (fun _ : ℝ => (0 : ℂ)) x ≠ 0} := by simp
  rcases paley_wiener_whitney_joint_interpolation (∅ : Set ℝ) Set.countable_empty h_sep_empty (fun _ => 0) h_vfin_empty T hT w with ⟨f, _, h_melin⟩
  exact ⟨f, h_melin⟩"""

content = content.replace(old_countable, new_finite)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print('Interpolation.lean updated')
