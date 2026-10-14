import Mathlib.Algebra.Module.Torsion.Basic

/-!
# 引理 A.1：p-挠平凡 ⟹ p-准素部分平凡（BSD.ShaPComponent）

对应《Iwasawa 欧拉系延伸路线》§2 阶段 A（免费层闭合）：

    G[p] = 0  ⟹  G[p^∞] = 0

数学证明（最小 p-幂阶论证）：
  若 x ∈ G[p^∞]（∃ n, pⁿ·x = 0）且 x ≠ 0，取最小 n ≥ 1 使 pⁿ·x = 0；
  则 y = p^(n−1)·x ≠ 0（最小性）且 p·y = pⁿ·x = 0，故 y ∈ G[p] = 0，矛盾。

本文件为**纯群论真证层**（不依赖任何 BSD axiom；仅用 mathlib 的
挠子群 / nsmul / 子群基础）。

应用（descent 层，路线 §4）：389a1, p=2 实例——
|Sel₂| = 4 = 2^rank（三次域复算，Probe389/sel2_final.py）⟹ |Ш[2]| = 1
⟹ 引理 A.1 ⟹ Ш[2^∞](E/K) = 0（Ш[2] = 0 ⟹ 2-准素部分平凡）。
边界（路线 §2 阶段 C）：这不给 λ_2 = 0（K_cyc 上 Sel 的 corank 增长
是独立的开放项，Iwasawa 主猜想侧）。
-/

namespace BSD.ShaPComponent

/-- p-准素子群（p-primary component）：由"阶为 p 的幂"的元素组成。
    x ∈ pPrimaryComponent A p ⟺ ∃ n : ℕ, p ^ n • x = 0。 -/
def pPrimaryComponent (A : Type*) [AddCommGroup A] (p : ℕ) : AddSubgroup A where
  carrier := {x | ∃ n : ℕ, p ^ n • x = 0}
  zero_mem' := by
    change ∃ n : ℕ, p ^ n • (0 : A) = 0
    exact ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy
    change ∃ n : ℕ, p ^ n • (x + y) = 0
    rcases hx with ⟨nx, hx0⟩
    rcases hy with ⟨ny, hy0⟩
    refine ⟨nx + ny, ?_⟩
    rw [nsmul_add]
    -- p^(nx+ny) • x = p^ny • (p^nx • x) = p^ny • 0 = 0
    have hx1 : p ^ (nx + ny) • x = 0 := by
      calc
        p ^ (nx + ny) • x = (p ^ nx * p ^ ny) • x := by rw [pow_add]
        _ = p ^ ny • (p ^ nx • x) := by rw [mul_nsmul]
        _ = p ^ ny • 0 := by rw [hx0]
        _ = 0 := by simp
    -- p^(nx+ny) • y = p^nx • (p^ny • y) = p^nx • 0 = 0
    have hy1 : p ^ (nx + ny) • y = 0 := by
      calc
        p ^ (nx + ny) • y = (p ^ ny * p ^ nx) • y := by
          rw [pow_add, mul_comm]
        _ = p ^ nx • (p ^ ny • y) := by rw [mul_nsmul]
        _ = p ^ nx • 0 := by rw [hy0]
        _ = 0 := by simp
    rw [hx1, hy1]
    simp
  neg_mem' := by
    intro x hx
    change ∃ n : ℕ, p ^ n • (-x) = 0
    rcases hx with ⟨n, hx0⟩
    refine ⟨n, ?_⟩
    rw [neg_nsmul, hx0]
    simp

@[simp]
lemma mem_pPrimaryComponent_iff {A : Type*} [AddCommGroup A] (p : ℕ) (x : A) :
    x ∈ pPrimaryComponent A p ↔ ∃ n : ℕ, p ^ n • x = 0 :=
  Iff.rfl

/-- **引理 A.1**：p-挠子群平凡 ⟹ p-准素部分平凡。
    证明：取最小 n ≥ 1 使 pⁿ·x = 0（Nat.find）；y = p^(n−1)·x 满足
    y ≠ 0（最小性）且 p·y = pⁿ·x = 0，故 y ∈ A[p] = ⊥，矛盾。 -/
theorem pPrimaryComponent_eq_bot_of_torsionBy_eq_bot {A : Type*} [AddCommGroup A] (p : ℕ)
    (h : AddSubgroup.torsionBy A (p : ℤ) = ⊥) :
    pPrimaryComponent A p = ⊥ := by
  classical
  rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  rw [mem_pPrimaryComponent_iff] at hx
  rcases hx with ⟨n, hn⟩
  by_contra hx_ne
  let hEx : ∃ n : ℕ, p ^ n • x = 0 := ⟨n, hn⟩
  let n0 : ℕ := Nat.find hEx
  have hn0 : p ^ n0 • x = 0 := Nat.find_spec hEx
  have hn0_pos : 0 < n0 := by
    by_contra hpos
    have hn0eq : n0 = 0 := Nat.eq_zero_of_not_pos hpos
    rw [hn0eq] at hn0
    simp at hn0
    exact hx_ne hn0
  let y : A := p ^ (n0 - 1) • x
  have hpy : p • y = 0 := by
    calc
      p • y = (p ^ (n0 - 1) * p) • x := by
        dsimp [y]
        rw [← mul_nsmul]
      _ = (p * p ^ (n0 - 1)) • x := by rw [mul_comm]
      _ = p ^ (n0 - 1 + 1) • x := by rw [pow_succ']
      _ = p ^ n0 • x := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hn0_pos)]
      _ = 0 := hn0
  have hy_mem : y ∈ AddSubgroup.torsionBy A (p : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    exact hpy
  have hy0 : y = 0 := by
    have h_el : ∀ x : A, x ∈ AddSubgroup.torsionBy A (p : ℤ) → x = 0 := by
      rw [AddSubgroup.eq_bot_iff_forall] at h
      exact h
    exact h_el y hy_mem
  have hy_ne : y ≠ 0 := by
    intro hy0'
    have hsmall : p ^ (n0 - 1) • x = 0 := by
      dsimp [y] at hy0'
      exact hy0'
    have hle : n0 ≤ n0 - 1 := Nat.find_min' hEx hsmall
    exact (not_lt_of_ge hle) (Nat.pred_lt (Nat.ne_of_gt hn0_pos))
  exact hy_ne hy0

end BSD.ShaPComponent
