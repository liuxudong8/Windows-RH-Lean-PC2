import OrderPreservingBijection.stage_4
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace TestObstacles

open RHSpectralDuality

-- 障碍 2：riemannZeta 共轭性质（mathlib ZetaAsymp.lean:461）
lemma riemannZeta_conj : ∀ (s : ℂ), _root_.riemannZeta (star s) = star (_root_.riemannZeta s) := by
  intro s
  exact _root_.riemannZeta_conj s

-- 下半平面共轭引理
lemma lower_conj_eq_upper (T : ℝ) (hT : 0 < T) :
    star '' {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0} =
    {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} := by
  ext s
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz1 : _root_.riemannZeta z = 0 := hz.1
    have hz2 : 0 < z.re := hz.2.1
    have hz3 : z.re < 1 := hz.2.2.1
    have hz4 : -T ≤ z.im := hz.2.2.2.1
    have hz5 : z.im ≤ 0 := hz.2.2.2.2
    have h1 : _root_.riemannZeta (star z) = 0 := by
      rw [riemannZeta_conj z, hz1] <;> simp
    have h2 : (star z).re = z.re := by simp
    have h3 : (star z).im = -z.im := by simp
    exact ⟨h1, by rw [h2] <;> exact hz2, by rw [h2] <;> exact hz3, by rw [h3] <;> linarith, by rw [h3] <;> linarith⟩
  · intro hs
    have hs1 : _root_.riemannZeta s = 0 := hs.1
    have hs2 : 0 < s.re := hs.2.1
    have hs3 : s.re < 1 := hs.2.2.1
    have hs4 : 0 ≤ s.im := hs.2.2.2.1
    have hs5 : s.im ≤ T := hs.2.2.2.2
    refine' ⟨star s, _ , _⟩
    · have h1 : _root_.riemannZeta (star s) = 0 := by
        rw [riemannZeta_conj s, hs1] <;> simp
      have h2 : (star s).re = s.re := by simp
      have h3 : (star s).im = -s.im := by simp
      exact ⟨h1, by rw [h2] <;> exact hs2, by rw [h2] <;> exact hs3, by rw [h3] <;> linarith, by rw [h3] <;> linarith⟩
    · simp

#check lower_conj_eq_upper

end TestObstacles
