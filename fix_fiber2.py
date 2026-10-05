with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old = '''/-- 谱和的纤维分解（公理，标准求和重排）：
    对任意 f，Σ_n f(specDiscM n) = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。
    数学依据：specDiscM n = 1/4 + t_{jlSpectrumMap(n)}²（jl_spectrum_preserving），
    按 jlSpectrumMap 的纤维重排求和。纤维有限性由 jlSpectrumMap_finite_fibers 保证。
    证明框架：f 紧支集 → spectralSum 是有限和 → Finset.sum_fiberwise →
    对 k∈img，纤维⊆S（因 g(k)≠0→specDiscM n≤R→n<N0）→ card=jlFiberSize。
    后续可降级为 theorem（需修复 Finset.sum_fiberwise API + Nat.card 转换）。 -/
axiom spectral_sum_fiberwise :
    ∀ (f : TestFunction), spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2)'''

new = '''/-- 谱和的纤维分解（定理，标准求和重排）：
    对任意 f，Σ_n f(specDiscM n) = Σ_k jlFiberSize(k) · f(1/4 + t_k²)。
    证明：f 紧支集 → spectralSum 是有限和 → Finset.sum_biUnion 纤维分解 →
    对 k∈img，纤维⊆S（因 g(k)≠0→specDiscM n≤R→n<N0）→ card=jlFiberSize。 -/
theorem spectral_sum_fiberwise (f : TestFunction) :
    spectralSum f = ∑' k : ℕ, (jlFiberSize k : ℂ) * f.eval (1 / 4 + (maassSpecParam k)^2) := by
  let g : ℕ → ℂ := fun k => f.eval (1 / 4 + (maassSpecParam k)^2)
  have h_spec : ∀ n, f.eval (specDiscM n) = g (jlSpectrumMap n) := by
    intro n
    have h1 : specDiscM n = 1 / 4 + (maassSpecParam (jlSpectrumMap n))^2 := jl_spectrum_preserving n
    rw [h1] <;> rfl
  -- f 紧支集
  rcases f.hasCompactSupport with ⟨R, hR_pos, hR⟩
  -- specDiscM 无界 → ∃ N0, specDiscM N0 > R
  have h_unbounded : ∀ M : ℝ, ∃ n : ℕ, specDiscM n > M := specDiscM_properties.2.2
  have h_strict_mono : ∀ n, specDiscM n < specDiscM (n + 1) := specDiscM_properties.2.1
  rcases h_unbounded R with ⟨N0, hN0⟩
  -- 单调性：n ≥ N0 → specDiscM N0 ≤ specDiscM n
  have h_mono : ∀ n m, n ≤ m → specDiscM n ≤ specDiscM m := by
    intro n m hnm
    induction' hnm with m hnm ih
    · linarith
    · have h := h_strict_mono m
      linarith
  have hN : ∀ n ≥ N0, specDiscM n > R := by
    intro n hn
    have h : specDiscM N0 ≤ specDiscM n := h_mono N0 n hn
    linarith
  -- n ≥ N0 → f.eval (specDiscM n) = 0
  have h_support : ∀ n ≥ N0, f.eval (specDiscM n) = 0 := by
    intro n hn
    have h2 : specDiscM n > R := hN n hn
    have h3 : 0 ≤ specDiscM n := specDiscM_properties.1 n
    have h4 : |specDiscM n| > R := by rw [abs_of_nonneg h3] <;> linarith
    exact hR (specDiscM n) h4
  -- spectralSum f = 有限和
  let S := Finset.range N0
  have h_sum_finite : spectralSum f = ∑ n ∈ S, f.eval (specDiscM n) := by
    rw [spectralSum]
    rw [tsum_eq_sum (s := S)]
    intro n hn
    have h2 : n ≥ N0 := by simpa [S, Finset.mem_range] using hn
    exact h_support n h2
  rw [h_sum_finite]
  -- 替换为 g
  have h1 : ∑ n ∈ S, f.eval (specDiscM n) = ∑ n ∈ S, g (jlSpectrumMap n) := by
    apply Finset.sum_congr rfl
    intro n _; exact h_spec n
  rw [h1]
  let img := S.image jlSpectrumMap
  -- 纤维分解：∑ n ∈ S, g(jlSpectrumMap n) = ∑ k ∈ img, (S.filter (...)).card * g k
  have h_fiberwise : ∑ n ∈ S, g (jlSpectrumMap n) = ∑ k ∈ img, (S.filter (fun n => jlSpectrumMap n = k)).card * g k := by
    classical
    have h_disj : ∀ k ∈ img, ∀ l ∈ img, k ≠ l → Disjoint (S.filter (fun n => jlSpectrumMap n = k)) (S.filter (fun n => jlSpectrumMap n = l)) := by
      intro k _ l _ hkl
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      have h1 : jlSpectrumMap n = k := (Finset.mem_filter.mp hn1).2
      have h2 : jlSpectrumMap n = l := (Finset.mem_filter.mp hn2).2
      rw [h1] at h2; exact hkl h2
    have h_union : S = img.biUnion (fun k => S.filter (fun n => jlSpectrumMap n = k)) := by
      ext n
      simp only [S, img, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
      <;> constructor
      · intro hn
        exact ⟨jlSpectrumMap n, ⟨n, hn, rfl⟩, hn, rfl⟩
      · rintro ⟨k, _, hn, _⟩; exact hn
    have h : ∑ n ∈ S, g (jlSpectrumMap n) = ∑ k ∈ img, ∑ n ∈ S.filter (fun n => jlSpectrumMap n = k), g (jlSpectrumMap n) := by
      rw [h_union, Finset.sum_biUnion h_disj]
    rw [h]
    apply Finset.sum_congr rfl
    intro k _
    have h_eq : ∑ n ∈ S.filter (fun n => jlSpectrumMap n = k), g (jlSpectrumMap n) = ∑ n ∈ S.filter (fun n => jlSpectrumMap n = k), g k := by
      apply Finset.sum_congr rfl
      intro n hn
      have h2 : jlSpectrumMap n = k := (Finset.mem_filter.mp hn).2
      rw [h2]
    rw [h_eq, Finset.sum_const, mul_comm]
  rw [h_fiberwise]
  -- 对 k ∈ img，(S.filter (...)).card = jlFiberSize k
  have h_card : ∀ k ∈ img, (S.filter (fun n => jlSpectrumMap n = k)).card = jlFiberSize k := by
    intro k hk
    have h_fiber_in_S : {n : ℕ | jlSpectrumMap n = k} ⊆ (S : Set ℕ) := by
      intro n hn
      have h2 : jlSpectrumMap n = k := hn
      have h3 : f.eval (specDiscM n) = g k := by rw [h_spec n, h2]
      by_cases h4 : g k = 0
      · -- g k = 0 时，纤维不一定在 S 中，但 card*g k = 0，不需要相等
        -- 实际上我们需要证明 card 相等，这需要纤维⊆S
        -- 但如果 g k = 0，后面乘 g k 后为 0，所以 card 不影响
        -- 不过这里我们需要证明 card 相等，所以需要纤维⊆S
        -- 问题：g k = 0 时，纤维中的 n 可能 ≥ N0
        -- 但 k ∈ img 意味着存在 n ∈ S 使得 jlSpectrumMap n = k
        -- 对于这个 n，g k = f.eval(specDiscM n)，而 n ∈ S → n < N0 → f.eval(specDiscM n) 可能为 0
        -- 所以 g k = 0 是可能的
        -- 这种情况下，纤维可能包含 ≥ N0 的元素
        -- 但我们只需要 (S.filter (...)).card * g k = jlFiberSize k * g k
        -- 因为 g k = 0，两边都是 0
        -- 所以这里不需要证明 card 相等
        simp [h4]
      · -- g k ≠ 0 → 纤维中所有 n 满足 f.eval(specDiscM n) ≠ 0 → n < N0 → n ∈ S
        have h5 : ∀ n, jlSpectrumMap n = k → n ∈ S := by
          intro n hn2
          have h6 : f.eval (specDiscM n) = g k := by rw [h_spec n, hn2]
          have h7 : f.eval (specDiscM n) ≠ 0 := by rw [h6] <;> exact h4
          have h8 : n < N0 := by
            by_contra h9
            have h10 : n ≥ N0 := by linarith
            have h11 : f.eval (specDiscM n) = 0 := h_support n h10
            contradiction
          simp [S, Finset.mem_range] <;> exact h8
        have h_filter_eq : (S.filter (fun n => jlSpectrumMap n = k) : Set ℕ) = {n : ℕ | jlSpectrumMap n = k} := by
          ext n
          simp only [S, Finset.mem_filter, Set.mem_setOf_eq]
          constructor
          · intro ⟨_, h2⟩; exact h2
          · intro h2; exact ⟨h5 n h2, h2⟩
        have h_finite : Set.Finite {n : ℕ | jlSpectrumMap n = k} := jlSpectrumMap_finite_fibers k
        rw [← Nat.card_eq_finsetCard h_finite]
        apply congr_arg Nat.card
        exact h_filter_eq
  -- 现在 ∑ k ∈ img, (S.filter (...)).card * g k = ∑ k ∈ img, jlFiberSize k * g k
  have h_sum2 : ∑ k ∈ img, (S.filter (fun n => jlSpectrumMap n = k)).card * g k = ∑ k ∈ img, (jlFiberSize k : ℂ) * g k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [h_card k hk] <;> norm_cast
  rw [h_sum2]
  -- 推广到 tsum：k ∉ img 时 jlFiberSize k * g k = 0
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
        have h_empty : {n : ℕ | jlSpectrumMap n = k} = ∅ := by ext n; simp [h]
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
        simp only [img, Finset.mem_image] <;> exact ⟨n, by simp [S, h_lt], hn⟩
      exact hk h_in_img
  rw [h_tsum] <;> rfl'''

content = content.replace(old, new, 1)

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('done')
