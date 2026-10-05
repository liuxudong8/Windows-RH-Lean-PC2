from pathlib import Path
p = Path(r"c:\proj2\OrderPreservingBijection\MellinInfrastructure.lean")
t = p.read_text(encoding="utf-8")
start = t.index("lemma mellin_integrand_integrable")
end = t.index("/-- Mellin 变换的线性性")
new = """lemma mellin_integrand_integrable (f : TestFunction) (s : ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  rcases f.hasCompactSupport with ⟨C, hC, hf⟩
  rcases f.vanishesNearZero with ⟨ε, hε, hεf⟩
  let K := Set.Icc ε C
  have hK : IsCompact K := isCompact_Icc
  have hK_sub : K ⊆ Set.Ioi (0:ℝ) := by intro x hx; linarith
  have h_eq : (fun x : ℝ => if 0 < x then f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ)) else 0) =
      Set.indicator K (fun x : ℝ => f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ))) := by
    funext x
    by_cases hx : x ∈ K
    · simp [hx, hK_sub]
    · have h1 : x ∉ Set.Icc ε C := hx
      have h2 : f.eval x = 0 := by
        by_cases h3 : 0 ≤ x
        · by_cases h4 : x ≤ C
          · by_cases h5 : x < ε
            · exact hεf x h5
            · have h6 : x ∈ K := by exact ⟨by linarith, h4⟩; exact False.elim (h1 h6)
          · exact hf x (by linarith)
        · simp
      simp [h2, h1, hK_sub] <;> ring
  rw [h_eq]
  have h_cont : ContinuousOn (fun x : ℝ => f.eval x * Complex.exp ((s - 1) * (Real.log x : ℂ))) K := by
    fun_prop <;> exact continuousOn_log.mono (fun x hx => by linarith [hx.1])
  exact h_cont.integrableOn_compact hK |>.indicator

"""
t = t[:start] + new + t[end:]
p.write_text(t, encoding="utf-8")
print("done")
