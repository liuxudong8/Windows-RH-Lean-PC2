  have h_mellin_eq : melinTransform h.toTestFunction s = (1:ℂ)/(s*(s+1)) * ∫ x in Set.Icc ε₀ R₀, f x := by
    -- M[h](s) = ∫_0^∞ h(x) x^{s-1} dx
    -- 因为 h 在 [0,ε₀) 和 (R₀,∞) 为 0，所以 = ∫_{ε₀}^{R₀} h(x) x^{s-1} dx
    have h_support : ∀ x, x ∉ Set.Icc ε₀ R₀ → h.toFun x = 0 := by
      intro x hx
      by_cases h1 : x < ε₀
      · exact h_left x h1
      · by_cases h2 : x > R₀
        · exact h_right x h2
        · have : x ∈ Set.Icc ε₀ R₀ := by
            exact ⟨by linarith, by linarith⟩
          contradiction
    -- 第一次分部积分：u=h, dv=x^{s-1}dx, v=x^s/s
    -- ∫ h x^{s-1} = [h x^s/s]_{ε₀}^{R₀} - (1/s) ∫ h' x^s
    -- 边界项 = h(R₀) R₀^s/s - h(ε₀) ε₀^s/s = 0
    -- 第二次分部积分：u=h', dv=x^s dx, v=x^{s+1}/(s+1)
    -- ∫ h' x^s = [h' x^{s+1}/(s+1)]_{ε₀}^{R₀} - 1/(s+1) ∫ h'' x^{s+1}
    -- 边界项 = h'(R₀) R₀^{s+1}/(s+1) - h'(ε₀) ε₀^{s+1}/(s+1) = 0
    -- 所以 M[h](s) = 1/(s(s+1)) ∫ h'' x^{s+1}
    admit
