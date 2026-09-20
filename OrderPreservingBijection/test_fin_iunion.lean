import OrderPreservingBijection.stage_4

namespace OrderPreservingBijection
namespace RHSpectralDuality

open OrderPreservingBijection

/-- 辅助：有限类型上可数集合的 iUnion 可数。 -/
lemma finite_iUnion_countable {α : Type*} [Fintype α] {β : Type*} {f : α → Set β}
    (h : ∀ i, Set.Countable (f i)) : Set.Countable (⋃ i : α, f i) := by
  have h1 : (⋃ i : α, f i) = ⋃ i ∈ (↑(Finset.univ : Finset α) : Set α), f i := by
    ext x; simp
  rw [h1]
  have h2 : (↑(Finset.univ : Finset α) : Set α).Finite := Finset.finite_toSet _
  have h3 : (↑(Finset.univ : Finset α) : Set α).Countable := Set.Finite.countable h2
  exact Set.Countable.biUnion h3 (fun i _ => h i)

-- 测试
lemma test_fin_iUnion : Set.Countable (⋃ i : Fin 3, (∅ : Set ℕ)) := by
  apply finite_iUnion_countable
  intro i
  exact Set.countable_empty

end RHSpectralDuality
end OrderPreservingBijection
