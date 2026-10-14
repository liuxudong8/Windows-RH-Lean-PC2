import Mathlib.GroupTheory.Index

/-!
# 剩余免费层项：descent 正合列基数 与 Cassels 配对（BSD.ShaFreeLayer）

对应《Iwasawa 欧拉系延伸路线》§4（阶段 A：免费层闭合）的剩余两项：

## 1. descent 正合列（真证：基数层）

descent 序列  0 → E(K)/pⁿE(K) → Sel_{pⁿ} → Ш[pⁿ] → 0
的抽象形式：0 →+ A --f--> B --g--> C →+ 0（f 单、g 满、range f = ker g）
⟹  **Nat.card B = Nat.card A · Nat.card C**。

这是"可计算层"的核心免费事实：|Ш[pⁿ]| = |Sel_{pⁿ}| / |E(K)/pⁿE(K)|。
（389a1/p=2 数值：|Sel₂| = 4 = |E(K)/2E(K)| ⟹ |Ш[2]| = 1，见下 §3。）

## 2. Cassels 配对（结构真证 + 平方结论挂账）

- 结构层真证：交错双线性配对 b : G×G → T 的定义、非退化性、诱导同态
  G →+ Hom(G,T) 及其单射性（非退化）。
- 平方结论挂账（axiom）：非退化交错配对 ⟹ |G| 是平方
  （经典证明：Sylow 分解 + 双曲分解归纳 |G| = |⟨x⟩|²·|⟨x⟩^⊥/⟨x⟩|；
   完整 Lean 真证列为阶段 E 后续工程项）。

## 3. 389a1 / p = 2 实例（数值 axiom + 真证推导）

descent 基数（真证）+ 数值 axiom（|Sel₂| = 4 = |E(K)/2E(K)|，Probe389
三次域复算 + LMFDB）⟹ **|Ш[2]| = 1**（真证推导）。

边界（路线 §2/§4 不变）：这不给 λ_2 = 0（K_cyc 侧独立开放项）。
-/

namespace BSD.ShaFreeLayer

-- ============ 1. descent 正合列基数（真证） ============

/-- 短正合列 0 →+ A --f--> B --g--> C →+ 0（f 单、g 满、range f = ker g）
    的基数公式：Nat.card B = Nat.card A · Nat.card C。
    证明：B 上 ker g 的 Lagrange 分解（card_mul_index）+ 第一同构
    B/ker g ≃ range g = C + f 单 ⟹ range f ≃ A。 -/
theorem card_eq_mul_of_short_exact_add {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (h_exact : AddMonoidHom.range f = AddMonoidHom.ker g) :
    Nat.card B = Nat.card A * Nat.card C := by
  -- B = (ker g) × (B ⧸ ker g)：card_mul_index（index 定义 = card (B ⧸ ker g)）
  have h1 : Nat.card (AddMonoidHom.ker g) * Nat.card (B ⧸ AddMonoidHom.ker g) = Nat.card B :=
    AddSubgroup.card_mul_index (AddMonoidHom.ker g)
  -- card (ker g) = card (range f) = card A
  have hker : Nat.card (AddMonoidHom.ker g) = Nat.card A := by
    rw [← h_exact]
    exact (Nat.card_congr (AddMonoidHom.ofInjective (f := f) hf).toEquiv).symm
  -- card (B ⧸ ker g) = card (range g) = card C
  have hquot : Nat.card (B ⧸ AddMonoidHom.ker g) = Nat.card C := by
    have e : (B ⧸ AddMonoidHom.ker g) ≃+ ↥(AddMonoidHom.range g) :=
      QuotientAddGroup.quotientKerEquivRange g
    have htop : AddMonoidHom.range g = ⊤ := (AddMonoidHom.range_eq_top).mpr hg
    calc
      Nat.card (B ⧸ AddMonoidHom.ker g) = Nat.card (AddMonoidHom.range g) :=
        Nat.card_congr e.toEquiv
      _ = Nat.card (⊤ : AddSubgroup C) := by rw [htop]
      _ = Nat.card C := Nat.card_congr (AddSubgroup.topEquiv).toEquiv
  calc
    Nat.card B = Nat.card (AddMonoidHom.ker g) * Nat.card (B ⧸ AddMonoidHom.ker g) := h1.symm
    _ = Nat.card A * Nat.card C := by rw [hker, hquot]

-- ============ 2. Cassels 配对结构（真证） ============

/-- 交错双线性配对 b : G × G → T（双线性 + 交错 b(x,x) = 0）。
    Cassels 配对 Ш[pⁿ] × Ш[pⁿ] → ℚ/ℤ 的抽象形式。 -/
structure AlternatingPairing (G : Type*) [AddCommGroup G] (T : Type*) [AddCommGroup T] where
  toFun : G → G → T
  map_add_left : ∀ x y z : G, toFun (x + y) z = toFun x z + toFun y z
  map_add_right : ∀ x y z : G, toFun x (y + z) = toFun x y + toFun x z
  is_alt : ∀ x : G, toFun x x = 0

/-- 非退化（左非退化；对交错型与右非退化等价）：b(x, ·) ≡ 0 ⟹ x = 0。 -/
def Nondegenerate {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) : Prop :=
  ∀ x : G, (∀ y : G, b.toFun x y = 0) → x = 0

/-- 双线性在左变元的零：b(0, y) = 0。 -/
lemma toFun_zero_left {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) (y : G) : b.toFun (0 : G) y = 0 := by
  have hh := b.map_add_left (0 : G) (0 : G) y
  have hh' : b.toFun (0 : G) y = b.toFun (0 : G) y + b.toFun (0 : G) y := by simpa using hh
  have hcancel : b.toFun (0 : G) y + b.toFun (0 : G) y = b.toFun (0 : G) y + (0 : T) := by
    rw [hh'.symm, add_zero]
  exact add_left_cancel hcancel

/-- 双线性在右变元的零：b(x, 0) = 0。 -/
lemma toFun_zero_right {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) (x : G) : b.toFun x (0 : G) = 0 := by
  have hh := b.map_add_right x (0 : G) (0 : G)
  have hh' : b.toFun x (0 : G) = b.toFun x (0 : G) + b.toFun x (0 : G) := by simpa using hh
  have hcancel : b.toFun x (0 : G) + b.toFun x (0 : G) = b.toFun x (0 : G) + (0 : T) := by
    rw [hh'.symm, add_zero]
  exact add_left_cancel hcancel

/-- 双线性在右变元的消去：b(x, -y) = -b(x, y)。 -/
theorem toFun_neg_right {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) (x y : G) : b.toFun x (-y) = -b.toFun x y := by
  have h : b.toFun x y + b.toFun x (-y) = 0 := by
    have h01 : b.toFun x (y + (-y)) = 0 := by simpa using toFun_zero_right b x
    rw [b.map_add_right x y (-y)] at h01
    exact h01
  have h' : b.toFun x (-y) + b.toFun x y = 0 := by
    rw [add_comm]
    exact h
  exact eq_neg_of_add_eq_zero_left h'

/-- 双线性在左变元的消去：b(-x, y) = -b(x, y)。 -/
theorem toFun_neg_left {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) (x y : G) : b.toFun (-x) y = -b.toFun x y := by
  have h : b.toFun x y + b.toFun (-x) y = 0 := by
    have h01 : b.toFun (x + (-x)) y = 0 := by simpa using toFun_zero_left b y
    rw [b.map_add_left x (-x) y] at h01
    exact h01
  have h' : b.toFun (-x) y + b.toFun x y = 0 := by
    rw [add_comm]
    exact h
  exact eq_neg_of_add_eq_zero_left h'

/-- 固定左变元得到的同态 b(x, ·) : G →+ T。 -/
def leftHom {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) (x : G) : AddMonoidHom G T where
  toFun := b.toFun x
  map_zero' := toFun_zero_right b x
  map_add' := b.map_add_right x

/-- 由配对诱导的（左）同态 G →+ Hom(G, T)：x ↦ b(x, ·)。
    Nondegenerate 恰为此同态单射。 -/
def pairingHom {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) : G →+ (G →+ T) where
  toFun := leftHom b
  map_zero' := by
    ext y
    exact toFun_zero_left b y
  map_add' := by
    intro x y
    ext z
    change b.toFun (x + y) z = b.toFun x z + b.toFun y z
    exact b.map_add_left x y z

/-- 非退化 ⟹ 诱导同态单射（Cassels 配对的基本性质，真证）。 -/
theorem injective_of_nondegenerate {G : Type*} [AddCommGroup G] {T : Type*} [AddCommGroup T]
    (b : AlternatingPairing G T) (hb : Nondegenerate b) :
    Function.Injective (pairingHom b) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hb
  intro z
  have hz : b.toFun x z = b.toFun y z := by
    change (pairingHom b x) z = (pairingHom b y) z
    exact DFunLike.congr_fun hxy z
  calc
    b.toFun (x - y) z = b.toFun (x + (-y)) z := by rw [sub_eq_add_neg]
    _ = b.toFun x z + b.toFun (-y) z := b.map_add_left x (-y) z
    _ = b.toFun x z + (-(b.toFun y z)) := by rw [toFun_neg_left]
    _ = 0 := by
      rw [hz]
      simp

/-- **Cassels 平方结论（axiom 挂账）**：非退化交错配对 ⟹ |G| 是平方。
    数学内容：有限阿贝尔群 G 上的非退化交错配对 ⟹ |G| = k²。
    经典证明：Sylow 分解 + 双曲分解归纳 |G| = |⟨x⟩|² · |⟨x⟩^⊥/⟨x⟩|。
    （完整 Lean 真证列为阶段 E 后续工程项；此处挂账以闭合免费层陈述。） -/
axiom card_square_of_nondegenerate_alternating {G : Type*} [AddCommGroup G] [Fintype G]
    {T : Type*} [AddCommGroup T] (b : AlternatingPairing G T) (hb : Nondegenerate b) :
    ∃ k : ℕ, Fintype.card G = k ^ 2

-- ============ 3. 389a1 / p = 2 实例（数值 axiom + 真证推导） ============

/-- E(K)/2E(K)（389a1，K = E[2] 分裂域）。数值：torsion 平凡 + rank 2
    ⟹ |E(K)/2E(K)| = 2^2 = 4（LMFDB 389a1 + Probe389 三次域复算）。 -/
axiom Ediv2_389 : Type
axiom Ediv2_389_group : AddCommGroup Ediv2_389
attribute [instance] Ediv2_389_group
axiom Ediv2_389_fintype : Fintype Ediv2_389
attribute [instance] Ediv2_389_fintype
axiom Ediv2_389_card : Fintype.card Ediv2_389 = 4

/-- Sel₂(389a1)。数值：|Sel₂| = 4 = 2^rank（Probe389/sel2_final.py
    三次域复算，与 Magma 手册例 H133E28 一致）。 -/
axiom Sel2_389 : Type
axiom Sel2_389_group : AddCommGroup Sel2_389
attribute [instance] Sel2_389_group
axiom Sel2_389_fintype : Fintype Sel2_389
attribute [instance] Sel2_389_fintype
axiom Sel2_389_card : Fintype.card Sel2_389 = 4

/-- Ш[2](E/K)。 -/
axiom Sha2_389 : Type
axiom Sha2_389_group : AddCommGroup Sha2_389
attribute [instance] Sha2_389_group
axiom Sha2_389_fintype : Fintype Sha2_389
attribute [instance] Sha2_389_fintype

/-- descent 正合列 0 → E(K)/2E(K) → Sel₂ → Ш[2] → 0（389a1）：
    映射与正合性挂账（descent 理论的标准结构）。 -/
axiom descent2_f : Ediv2_389 →+ Sel2_389
axiom descent2_g : Sel2_389 →+ Sha2_389
axiom descent2_f_injective : Function.Injective descent2_f
axiom descent2_g_surjective : Function.Surjective descent2_g
axiom descent2_exact : AddMonoidHom.range descent2_f = AddMonoidHom.ker descent2_g

/-- **|Ш[2]| = 1**：descent 基数（真证）+ 数值 axiom（|Sel₂| = |E(K)/2E(K)| = 4）。
    对应 Probe389 闭合链：|Sel₂| = 4 = 2^rank ⟹ |Ш[2]| = 1。
    （结合引理 A.1（ShaPComponent）：Ш[2] = 0 ⟹ Ш[2^∞](E/K) = 0。） -/
theorem sha2_389_card_eq_one : Fintype.card Sha2_389 = 1 := by
  have h1 := card_eq_mul_of_short_exact_add descent2_f descent2_g descent2_f_injective
    descent2_g_surjective descent2_exact
  -- h1 : Nat.card Sel2_389 = Nat.card Ediv2_389 * Nat.card Sha2_389
  simp only [Nat.card_eq_fintype_card] at h1
  rw [Ediv2_389_card, Sel2_389_card] at h1
  -- h1 : 4 = 4 * Fintype.card Sha2_389
  have h2 : 4 * Fintype.card Sha2_389 = 4 * 1 := by
    rw [mul_one]
    exact h1.symm
  exact Nat.mul_left_cancel (by decide : 0 < 4) h2

end BSD.ShaFreeLayer
