import re

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old = '''/-- 谱和的纤维分解（公理，标准求和重排）：
    对任意 f，Σ_n f(specDiscM n) = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。
    数学依据：specDiscM n = 1/4 + t_{jlSpectrumMap(n)}²（jl_spectrum_preserving），
    按 jlSpectrumMap 的纤维重排求和。纤维有限性由 jlSpectrumMap_finite_fibers 保证。
    后续可降级为 theorem（需 tsum_fiberwise + Summable 条件）。 -/
axiom spectral_sum_fiberwise :
    ∀ (f : TestFunction), spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2)'''

new = '''/-- 谱和的纤维分解（定理，标准求和重排）：
    对任意 f，Σ_n f(specDiscM n) = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。
    证明：f 紧支集 → spectralSum 是有限和 → Finset.sum_fiberwise 分解 →
    纤维有限性（jlSpectrumMap_finite_fibers）保证 jlFiberSize 正确。 -/
theorem spectral_sum_fiberwise (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) := by
  let g : ℕ → ℂ := fun k => f.eval (1 / 4 + (maassSpecParam k)^2)
  have h_spec : ∀ n, f.eval (specDiscM n) = g (jlSpectrumMap n) := by
    intro n
    have h1 : specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2 := jl_spectrum_preserving n
    rw [h1] <;> rfl
  -- f 紧支集 → 存在 R，|x| > R → f.eval x = 0
  rcases f.hasCompactSupport with ⟨R, hR_pos, hR⟩
  -- specDiscM 严格递增且无界 → 存在 N，n ≥ N → specDiscM n > R
  have h_spec_unbounded : ∀ M : ℝ, ∃ n : ℕ, specDiscM n > M :=
    (Classical.choose_spec laplacian_has_discrete_spectrum.2).2.2.2
  have h_spec_strict_mono : ∀ n, specDiscM n < specDiscM (n + 1) :=
    (Classical.choose_spec laplacian_has_discrete_spectrum.2).2.1
  rcases h_spec_unbounded R with ⟨N0, hN0⟩
  have hN : ∀ n ≥ N0, specDiscM n > R := by
    intro n hn
    have h : specDiscM N0 ≤ specDiscM n := by
      apply Nat.recOn (motive := fun k => specDiscM N0 ≤ specDiscM (N0 + k))
      · simp
      · intro k ih
        have h2 := h_spec_strict_mono (N0 + k)
        linarith
      exact?
    linarith
  -- 因此 n ≥ N0 → f.eval (specDiscM n) = 0
  have h_support : ∀ n ≥ N0, f.eval (specDiscM n) = 0 := by
    intro n hn
    have h2 : specDiscM n > R := hN n hn
    have h3 : |specDiscM n| > R := by
      have h4 : 0 ≤ specDiscM n := (Classical.choose_spec laplacian_has_discrete_spectrum.2).1 n
      rw [abs_of_nonneg h4] <;> linarith
    exact hR (specDiscM n) h3
  -- spectralSum f = ∑ n ∈ Finset.range N0, f.eval (specDiscM n)
  have h_sum_finite : spectralSum f = ∑ n ∈ Finset.range N0, f.eval (specDiscM n) := by
    rw [spectralSum]
    rw [tsum_eq_sum (s := Finset.range N0)]
    · intro n hn
      have h2 : n ≥ N0 := by simpa [Finset.mem_range] using hn
      exact h_support n h2
  rw [h_sum_finite]
  -- 用 h_spec 替换
  have h1 : ∑ n ∈ Finset.range N0, f.eval (specDiscM n) = ∑ n ∈ Finset.range N0, g (jlSpectrumMap n) := by
    apply Finset.sum_congr rfl
    intro n _
    exact h_spec n
  rw [h1]
  -- Finset.sum_fiberwise 分解
  let S := Finset.range N0
  let img := S.image jlSpectrumMap
  have h_fiberwise : ∑ n ∈ S, g (jlSpectrumMap n) = ∑ k ∈ img, ∑ n ∈ S.filter (fun n => jlSpectrumMap n = k), g k := by
    rw [Finset.sum_fiberwise_of_maps_to (by simp) (by simp)]
    <;> rfl
  rw [h_fiberwise]
  -- 对每个 k ∈ img，内层和 = jlFiberSize k * g k
  have h_inner : ∀ k ∈ img, ∑ n ∈ S.filter (fun n => jlSpectrumMap n = k), g k = (jlFiberSize k : ℂ) * g k := by
    intro k hk
    have h_fiber_in_S : {n : ℕ | jlSpectrumMap n = k} ⊆ (S : Set ℕ) := by
      intro n hn
      have h2 : jlSpectrumMap n = k := hn
      have h3 : f.eval (specDiscM n) = g k := by rw [h_spec n, h2]
      by_cases h4 : g k = 0
      · -- g k = 0，则 f.eval (specDiscM n) = 0，但 n 可能不在 S 中
        -- 实际上如果 g k = 0，内层和为 0，jlFiberSize k * g k = 0，不需要纤维在 S 中
        simp [h4]
      · -- g k ≠ 0，则 f.eval (specDiscM n) ≠ 0，所以 n < N0
        have h5 : f.eval (specDiscM n) ≠ 0 := by rw [h3] <;> exact h4
        have h6 : n < N0 := by
          by_contra h7
          have h8 : n ≥ N0 := by linarith
          have h9 : f.eval (specDiscM n) = 0 := h_support n h8
          contradiction
        simp [S, Finset.mem_range] <;> exact h6
    -- S.filter = 整个纤维（因为纤维 ⊆ S）
    have h_filter_eq : (S.filter (fun n => jlSpectrumMap n = k) : Set ℕ) = {n : ℕ | jlSpectrumMap n = k} := by
      ext n
      simp [S, Finset.mem_filter]
      <;> constructor <;> intro h <;> tauto
    have h_finite : Set.Finite {n : ℕ | jlSpectrumMap n = k} := jlSpectrumMap_finite_fibers k
    rw [Finset.sum_const]
    have h_card : (S.filter (fun n => jlSpectrumMap n = k)).card = jlFiberSize k := by
      rw [← Nat.card_eq_finsetCard h_finite]
      apply congr_arg Nat.card
      exact h_filter_eq
    rw [h_card] <;> ring
  rw [Finset.sum_congr rfl h_inner]
  -- 现在需要证明：∑ k ∈ img, jlFiberSize k * g k = ∑' k, jlFiberSize k * g k
  -- 对于 k ∉ img，如果 jlFiberSize k * g k ≠ 0，则 g k ≠ 0 且 jlFiberSize k > 0
  -- jlFiberSize k > 0 → 纤维非空 → 存在 n，jlSpectrumMap n = k
  -- g k ≠ 0 → f.eval (specDiscM n) ≠ 0 → n < N0 → k ∈ img，矛盾
  have h_tsum : ∑' k : ℕ, (jlFiberSize k : ℂ) * g k = ∑ k ∈ img, (jlFiberSize k : ℂ) * g k := by
    rw [tsum_eq_sum (s := img)]
    intro k hk
    by_cases hgk : g k = 0
    · simp [hgk]
    · -- g k ≠ 0，需要 jlFiberSize k = 0
      by_contra hf
      have hf' : jlFiberSize k ≠ 0 := by exact_mod_cast hf
      have h_nonempty : ∃ n, jlSpectrumMap n = k := by
        by_contra h
        have h_empty : {n : ℕ | jlSpectrumMap n = k} = ∅ := by
          ext n; simp [h]
        rw [jlFiberSize, h_empty] at hf'
        simp at hf' <;> tauto
      rcases h_nonempty with ⟨n, hn⟩
      have h_eval : f.eval (specDiscM n) = g k := by rw [h_spec n, hn]
      have h_ne : f.eval (specDiscM n) ≠ 0 := by rw [h_eval] <;> exact hgk
      have h_lt : n < N0 := by
        by_contra h7
        have h8 : n ≥ N0 := by linarith
        have h9 : f.eval (specDiscM n) = 0 := h_support n h8
        contradiction
      have h_in_img : k ∈ img := by
        simp [img, S, Finset.mem_image] <;> exact ⟨n, by simp [h_lt], hn⟩
      exact hk h_in_img
  rw [h_tsum] <;> rfl'''

content = content.replace(old, new, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
