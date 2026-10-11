import BSD.Positivity.Positivity
import BSD.LSeries5
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open scoped Topology

/-!
# 二阶 Leibniz 归约：leibniz_artin 的真定理化（BSD.LeibnizReduction）

对应分析（2026-10-11 讨论）：P* 的解析内容是 Artin 分解 L(E/K) = L(E)·L(E⁵)
的 Leibniz 三型。此前 `BSD.Positivity.leibniz_artin`（L″(E/K,1) = 组合）是
**挂账 axiom**——把"乘积二阶导"这个纯微积分事实放在假设里。本模块仿
`BSD.ExclusionReduction` §1 的模式把它升级：

## 模块分层

1. **通用二阶 Leibniz 三型真定理（纯微积分，闭包 = 逻辑公理）**：
   `product_second_deriv`（(f·g)″(1) = f″(1)·g(1) + 2·f′(1)·g′(1) + f(1)·g″(1)，
   需 f、g 在 1 二次可微，ContDiffAt 2）+ 三型消去
   `leibniz_20_second`（f(1)=f′(1)=0 ⟹ = f″(1)·g(1)）、
   `leibniz_02_second`（g(1)=g′(1)=0 ⟹ = f(1)·g″(1)）、
   `leibniz_11_second`（f(1)=g(1)=0 ⟹ = 2·f′(1)·g′(1)）
   与非零传播三型（`leibniz_*_second_ne_zero`）。
   证明用 ContDiffAt 2 的开邻域结构 + deriv_mul/deriv_add + HasDerivAt 链，
   无任何挂账。

2. **对象层（K = ℚ(√5)，Artin 分解锚定）**：单条组合 axiom
   `L_fun_structure`——存在 C² 函数 L_E_fun、L_EK_fun，
   L_EK_fun = L_E_fun · L_E5（Artin 分解），且 Positivity 的全部数值对象
   （中心值、一阶导、二阶导）都是这些函数在 s = 1 的对应值/导数值。
   数学依据：自守 L 函数在 s = 1 全纯（模性 Wiles + 解析延拓）+ 基变换
   L 函数恒等式——理论级真，Lean 内为实现缺口挂账（mathlib 无自守 L）。
   由此 **`leibniz_artin_theorem` 成为真定理**（闭包 = L_fun_structure + 逻辑，
   `BSD.Positivity.leibniz_artin` 数值恒等式 axiom 退役于本路线）。

3. **三型对象消去与 P* 镜像**：`leibniz_20/11/02_second_object`
   （在 (2,0)/(1,1)/(0,2) 型下 L″(E/K,1) = 单乘积/纠缠项，由泛型三型 +
   Positivity 的 Taylor 消元 axiom 推出）+ `p_star_type_*_via_leibniz` +
   `p_star_via_leibniz`（P* 的完整镜像，闭包不含 leibniz_artin，
   分量级 BSD 正性 axiom 仍是 P* 的数学假设面）。

闭包预期（#print axioms 实测见 _check_leibniz_reduction.lean）：
- §1 全零 axiom（纯逻辑公理）；
- `leibniz_artin_theorem` = L_fun_structure + 逻辑；
- `p_star_via_leibniz` = L_fun_structure + Positivity 分量正性/Taylor 族 + 逻辑，
  **不含 leibniz_artin、不含 bsd_formula_rank_\*、不含 GRH**。
-/

namespace BSD.LeibnizReduction

noncomputable section

/-! ## 1. 通用二阶 Leibniz 三型真定理（纯微积分） -/

/-- f 在 1 处二次可微：存在开邻域 v ∋ 1，f 在 v 上 C²。
    与 `ContDiffAt ℝ 2 f 1`（Taylor 级数定义）等价，但给出可 rcases 的
    邻域结构，是本模块二阶导证明的假设形态。 -/
def C2At (f : ℝ → ℝ) : Prop := ∃ v, v ∈ 𝓝 1 ∧ IsOpen v ∧ ContDiffOn ℝ 2 f v

/-- 二阶乘积求导（完整分解）：(f·g)″(1) = f″(1)·g(1) + 2·f′(1)·g′(1) + f(1)·g″(1)。
    需 f、g 在 1 二次可微（C2At）。这是 leibniz_artin 的微积分内容：
    Artin 分解 L(E/K) = L(E)·L(E⁵) 在解析侧的乘积求导。 -/
theorem product_second_deriv {f g : ℝ → ℝ}
    (hf : C2At f) (hg : C2At g) :
    deriv (deriv (fun s => f s * g s)) 1 =
      deriv (deriv f) 1 * g 1 + (2 : ℝ) * deriv f 1 * deriv g 1 +
        f 1 * deriv (deriv g) 1 := by
  -- 开邻域：∃ vf 开 ∋ 1，ContDiffOn 2 f vf
  rcases hf with ⟨vf, hvf_nhds, hvf_open, hfu⟩
  rcases hg with ⟨vg, hvg_nhds, hvg_open, hgu⟩
  let v : Set ℝ := vf ∩ vg
  have hfv : ContDiffOn ℝ 2 f v := hfu.mono (by intro s hs; exact hs.1)
  have hgv : ContDiffOn ℝ 2 g v := hgu.mono (by intro s hs; exact hs.2)
  have hv_open : IsOpen v := hvf_open.inter hvg_open
  have h1v : 1 ∈ v := ⟨mem_of_mem_nhds hvf_nhds, mem_of_mem_nhds hvg_nhds⟩
  have hv_nhds : v ∈ 𝓝 1 := hv_open.mem_nhds h1v
  -- C² ⟹ deriv 在 v 上 C¹（contDiffOn_succ_iff_deriv_of_isOpen，n = 1）
  have hfsplit : DifferentiableOn ℝ f v ∧ ((1 : WithTop ℕ∞) = ⊤ → AnalyticOn ℝ f v) ∧
      ContDiffOn ℝ 1 (deriv f) v := by
    have h1 : ContDiffOn ℝ (1 + 1) f v := hfv
    have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (s := v) (n := (1 : WithTop ℕ∞)) hv_open).1 h1
    exact h2
  have hgsplit : DifferentiableOn ℝ g v ∧ ((1 : WithTop ℕ∞) = ⊤ → AnalyticOn ℝ g v) ∧
      ContDiffOn ℝ 1 (deriv g) v := by
    have h1 : ContDiffOn ℝ (1 + 1) g v := hgv
    have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (s := v) (n := (1 : WithTop ℕ∞)) hv_open).1 h1
    exact h2
  have hdv_on : DifferentiableOn ℝ (deriv f) v :=
    hfsplit.2.2.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hdgv_on : DifferentiableOn ℝ (deriv g) v :=
    hgsplit.2.2.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  -- 逐点一阶可微与逐点乘积求导（v 内）
  have hpoint : ∀ s ∈ v, deriv (fun t => f t * g t) s = deriv f s * g s + f s * deriv g s := by
    intro s hs
    have hfd : DifferentiableAt ℝ f s :=
      (hfv.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt (hv_open.mem_nhds hs)
    have hgd : DifferentiableAt ℝ g s :=
      (hgv.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt (hv_open.mem_nhds hs)
    exact deriv_mul hfd hgd
  -- 事件等价：H =ᶠ[𝓝 1] (A·g + f·B)
  have hev : (fun s => deriv (fun t => f t * g t) s) =ᶠ[𝓝 1]
      (fun s => deriv f s * g s + f s * deriv g s) := by
    filter_upwards [hv_nhds] with s hs
    exact hpoint s hs
  -- 一阶与二阶 HasDerivAt（点 1）
  have hf1 : HasDerivAt f (deriv f 1) 1 :=
    ((hfv.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt (hv_open.mem_nhds h1v)).hasDerivAt
  have hg1 : HasDerivAt g (deriv g 1) 1 :=
    ((hgv.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt (hv_open.mem_nhds h1v)).hasDerivAt
  have hdf1 : HasDerivAt (deriv f) (deriv (deriv f) 1) 1 :=
    (hdv_on.differentiableAt (hv_open.mem_nhds h1v)).hasDerivAt
  have hdg1 : HasDerivAt (deriv g) (deriv (deriv g) 1) 1 :=
    (hdgv_on.differentiableAt (hv_open.mem_nhds h1v)).hasDerivAt
  -- 组合：A·g + f·B 的 HasDerivAt
  have hAg : HasDerivAt (fun s => deriv f s * g s)
      (deriv (deriv f) 1 * g 1 + deriv f 1 * deriv g 1) 1 := hdf1.mul hg1
  have hfB : HasDerivAt (fun s => f s * deriv g s)
      (deriv f 1 * deriv g 1 + f 1 * deriv (deriv g) 1) 1 := hf1.mul hdg1
  have hsum : HasDerivAt (fun s => deriv f s * g s + f s * deriv g s)
      (deriv (deriv f) 1 * g 1 + deriv f 1 * deriv g 1 +
        (deriv f 1 * deriv g 1 + f 1 * deriv (deriv g) 1)) 1 := hAg.add hfB
  -- H =ᶠ A·g + f·B 的局部性
  have hH : HasDerivAt (fun s => deriv (fun t => f t * g t) s)
      (deriv (deriv f) 1 * g 1 + deriv f 1 * deriv g 1 +
        (deriv f 1 * deriv g 1 + f 1 * deriv (deriv g) 1)) 1 :=
    hsum.congr_of_eventuallyEq hev
  calc
    deriv (deriv (fun s => f s * g s)) 1 =
        deriv (deriv f) 1 * g 1 + deriv f 1 * deriv g 1 +
          (deriv f 1 * deriv g 1 + f 1 * deriv (deriv g) 1) := hH.deriv
    _ = deriv (deriv f) 1 * g 1 + (2 : ℝ) * deriv f 1 * deriv g 1 +
        f 1 * deriv (deriv g) 1 := by ring

/-- Leibniz (2,0) 型消去：f(1) = f′(1) = 0 ⟹ (f·g)″(1) = f″(1)·g(1)。
    秩 2 P* 的 (2,0) 分支（rank E(ℚ) = 2，rank E⁵(ℚ) = 0）的解析内容：
    E 分量二阶零 + E⁵ 分量非零 ⟹ 乘积二阶导 = f″·g。 -/
theorem leibniz_20_second {f g : ℝ → ℝ}
    (hf : C2At f) (hg : C2At g)
    (hf0 : f 1 = 0) (hf1 : deriv f 1 = 0) :
    deriv (deriv (fun s => f s * g s)) 1 = deriv (deriv f) 1 * g 1 := by
  rw [product_second_deriv hf hg, hf0, hf1]
  ring

/-- Leibniz (0,2) 型消去（对称）：g(1) = g′(1) = 0 ⟹ (f·g)″(1) = f(1)·g″(1)。 -/
theorem leibniz_02_second {f g : ℝ → ℝ}
    (hf : C2At f) (hg : C2At g)
    (hg0 : g 1 = 0) (hg1 : deriv g 1 = 0) :
    deriv (deriv (fun s => f s * g s)) 1 = f 1 * deriv (deriv g) 1 := by
  rw [product_second_deriv hf hg, hg0, hg1]
  ring

/-- Leibniz (1,1) 型消去（纠缠项）：f(1) = g(1) = 0 ⟹ (f·g)″(1) = 2·f′(1)·g′(1)。
    秩 2 P* 的 (1,1) 分支——唯二非平凡项 2·f′·g′ 恰为两个 ℚ 侧秩 1 导数的纠缠。 -/
theorem leibniz_11_second {f g : ℝ → ℝ}
    (hf : C2At f) (hg : C2At g)
    (hf0 : f 1 = 0) (hg0 : g 1 = 0) :
    deriv (deriv (fun s => f s * g s)) 1 = (2 : ℝ) * deriv f 1 * deriv g 1 := by
  rw [product_second_deriv hf hg, hf0, hg0]
  ring

/-- (2,0) 型非零传播：f″(1) ≠ 0 ∧ g(1) ≠ 0 ⟹ (f·g)″(1) ≠ 0。 -/
theorem leibniz_20_second_ne_zero {f g : ℝ → ℝ}
    (hf : C2At f) (hg : C2At g)
    (hf0 : f 1 = 0) (hf1 : deriv f 1 = 0)
    (hf2 : deriv (deriv f) 1 ≠ 0) (hg0 : g 1 ≠ 0) :
    deriv (deriv (fun s => f s * g s)) 1 ≠ 0 := by
  rw [leibniz_20_second hf hg hf0 hf1]
  exact mul_ne_zero hf2 hg0

/-- (0,2) 型非零传播（对称）。 -/
theorem leibniz_02_second_ne_zero {f g : ℝ → ℝ}
    (hf : C2At f) (hg : C2At g)
    (hg0 : g 1 = 0) (hg1 : deriv g 1 = 0)
    (hf0 : f 1 ≠ 0) (hg2 : deriv (deriv g) 1 ≠ 0) :
    deriv (deriv (fun s => f s * g s)) 1 ≠ 0 := by
  rw [leibniz_02_second hf hg hg0 hg1]
  exact mul_ne_zero hf0 hg2

/-- (1,1) 型非零传播（纠缠）：f′(1) ≠ 0 ∧ g′(1) ≠ 0 ⟹ (f·g)″(1) ≠ 0。 -/
theorem leibniz_11_second_ne_zero {f g : ℝ → ℝ}
    (hf : C2At f) (hg : C2At g)
    (hf0 : f 1 = 0) (hg0 : g 1 = 0)
    (hf1 : deriv f 1 ≠ 0) (hg1 : deriv g 1 ≠ 0) :
    deriv (deriv (fun s => f s * g s)) 1 ≠ 0 := by
  rw [leibniz_11_second hf hg hf0 hg0]
  exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hf1) hg1

/-! ## 2. 对象层：Artin 分解锚定 + leibniz_artin 真定理化 -/

/-- P* 对象的函数层结构（挂账 axiom，实现缺口）：
    存在 C² 函数 L_E_fun（E/ℚ 的 L 函数）、L_EK_fun（E/K 的 L 函数），
    L_EK_fun = L_E_fun · L_E5（Artin 分解恒等式，Main.lean 注释的"待证明"项），
    且 Positivity 的全部数值对象（中心值、一阶导、二阶导）都是这些函数在
    s = 1 的对应值/导数值。
    数学依据：模性（Wiles）+ 解析延拓 ⟹ 自守 L 函数在 s = 1 全纯；
    Artin 分解是基变换的 L 函数恒等式。理论级真，Lean 内因 mathlib
    无自守 L 理论而挂账。
    升级路径：自守 L / 基变换理论入 mathlib 后本 axiom 分解为真定理。 -/
axiom L_fun_structure :
  ∃ (L_E_fun : ℝ → ℝ) (L_EK_fun : ℝ → ℝ),
    L_EK_fun = (fun s => L_E_fun s * BSD.LSeries5.L_E5 s) ∧
    C2At L_E_fun ∧
    C2At (BSD.LSeries5.L_E5) ∧
    C2At L_EK_fun ∧
    BSD.Positivity.Lprimeprime_EK_one = deriv (deriv L_EK_fun) 1 ∧
    BSD.Positivity.Lprimeprime_E_one = deriv (deriv L_E_fun) 1 ∧
    BSD.Positivity.Lprimeprime_E5_one = deriv (deriv (BSD.LSeries5.L_E5)) 1 ∧
    BSD.Positivity.Lprime_E_one = deriv L_E_fun 1 ∧
    BSD.Positivity.Lprime_E5_one = deriv (BSD.LSeries5.L_E5) 1 ∧
    BSD.Positivity.LE_one = L_E_fun 1 ∧
    BSD.Positivity.LE5_one = BSD.LSeries5.L_E5 1

/-- **leibniz_artin 真定理化**：Leibniz 恒等式（L″(E/K,1) = L″(E,1)·L(E⁵,1)
    + 2·L′(E,1)·L′(E⁵,1) + L(E,1)·L″(E⁵,1)）由 L_fun_structure +
    `product_second_deriv` 推出——`BSD.Positivity.leibniz_artin`（数值恒等式
    axiom）在本路线退役。闭包 = L_fun_structure + 逻辑公理。 -/
theorem leibniz_artin_theorem :
    BSD.Positivity.Lprimeprime_EK_one =
      BSD.Positivity.Lprimeprime_E_one * BSD.Positivity.LE5_one +
        (2 : ℝ) * BSD.Positivity.Lprime_E_one * BSD.Positivity.Lprime_E5_one +
          BSD.Positivity.LE_one * BSD.Positivity.Lprimeprime_E5_one := by
  rcases L_fun_structure with ⟨Lf, LKf, hEK, hf2, hg2, hK2, hppEK, hppE, hppE5,
    hpE, hpE5, hLE, hLE5⟩
  calc
    BSD.Positivity.Lprimeprime_EK_one = deriv (deriv LKf) 1 := hppEK
    _ = deriv (deriv (fun s => Lf s * BSD.LSeries5.L_E5 s)) 1 := by rw [hEK]
    _ = deriv (deriv Lf) 1 * BSD.LSeries5.L_E5 1 +
        (2 : ℝ) * deriv Lf 1 * deriv (BSD.LSeries5.L_E5) 1 +
          Lf 1 * deriv (deriv (BSD.LSeries5.L_E5)) 1 := by
      exact product_second_deriv hf2 hg2
    _ = BSD.Positivity.Lprimeprime_E_one * BSD.Positivity.LE5_one +
        (2 : ℝ) * BSD.Positivity.Lprime_E_one * BSD.Positivity.Lprime_E5_one +
          BSD.Positivity.LE_one * BSD.Positivity.Lprimeprime_E5_one := by
      rw [← hppE, ← hLE5, ← hpE, ← hpE5, ← hLE, ← hppE5]

/-! ## 3. 三型对象消去与 P* 镜像 -/

/-- (2,0) 型对象消去：rank E(ℚ) = 2 ∧ rank E⁵(ℚ) = 0 ⟹ L″(E/K,1) = L″(E,1)·L(E⁵,1)。
    消去依据：zeroOrderE = 2 ⟹ L(E,1) = 0（`L_value_zero_of_rank_pos`）与
    L′(E,1) = 0（`Lprime_zero_of_rank_ne_one`）——Taylor 消元 axiom（Positivity 已有）。 -/
theorem leibniz_20_second_object (hE2 : BSD.Positivity.zeroOrderE = 2)
    (_hE5_0 : BSD.Positivity.zeroOrderE5 = 0) :
    BSD.Positivity.Lprimeprime_EK_one =
      BSD.Positivity.Lprimeprime_E_one * BSD.Positivity.LE5_one := by
  rcases L_fun_structure with ⟨Lf, LKf, hEK, hf2, hg2, hK2, hppEK, hppE, hppE5,
    hpE, hpE5, hLE, hLE5⟩
  have hLE0 : BSD.Positivity.LE_one = 0 :=
    BSD.Positivity.L_value_zero_of_rank_pos (by simp [hE2])
  have hLpE0 : BSD.Positivity.Lprime_E_one = 0 :=
    BSD.Positivity.Lprime_zero_of_rank_ne_one (by simp [hE2])
  have hLf0 : Lf 1 = 0 := by rw [hLE] at hLE0; exact hLE0
  have hLf'0 : deriv Lf 1 = 0 := by rw [hpE] at hLpE0; exact hLpE0
  calc
    BSD.Positivity.Lprimeprime_EK_one = deriv (deriv LKf) 1 := hppEK
    _ = deriv (deriv (fun s => Lf s * BSD.LSeries5.L_E5 s)) 1 := by rw [hEK]
    _ = deriv (deriv Lf) 1 * BSD.LSeries5.L_E5 1 := by
      exact leibniz_20_second hf2 hg2 hLf0 hLf'0
    _ = BSD.Positivity.Lprimeprime_E_one * BSD.Positivity.LE5_one := by
      rw [← hppE, ← hLE5]

/-- (0,2) 型对象消去：rank E(ℚ) = 0 ∧ rank E⁵(ℚ) = 2 ⟹ L″(E/K,1) = L(E,1)·L″(E⁵,1)。 -/
theorem leibniz_02_second_object (_hE0 : BSD.Positivity.zeroOrderE = 0)
    (hE5_2 : BSD.Positivity.zeroOrderE5 = 2) :
    BSD.Positivity.Lprimeprime_EK_one =
      BSD.Positivity.LE_one * BSD.Positivity.Lprimeprime_E5_one := by
  rcases L_fun_structure with ⟨Lf, LKf, hEK, hf2, hg2, hK2, hppEK, hppE, hppE5,
    hpE, hpE5, hLE, hLE5⟩
  have hLE5_0 : BSD.Positivity.LE5_one = 0 :=
    BSD.Positivity.L_value_zero_of_rank_pos5 (by simp [hE5_2])
  have hLpE5_0 : BSD.Positivity.Lprime_E5_one = 0 :=
    BSD.Positivity.Lprime_zero_of_rank_ne_one5 (by simp [hE5_2])
  have hLg0 : BSD.LSeries5.L_E5 1 = 0 := by rw [hLE5] at hLE5_0; exact hLE5_0
  have hLg'0 : deriv (BSD.LSeries5.L_E5) 1 = 0 := by rw [hpE5] at hLpE5_0; exact hLpE5_0
  calc
    BSD.Positivity.Lprimeprime_EK_one = deriv (deriv LKf) 1 := hppEK
    _ = deriv (deriv (fun s => Lf s * BSD.LSeries5.L_E5 s)) 1 := by rw [hEK]
    _ = deriv (deriv Lf) 1 * BSD.LSeries5.L_E5 1 +
        (2 : ℝ) * deriv Lf 1 * deriv (BSD.LSeries5.L_E5) 1 +
          Lf 1 * deriv (deriv (BSD.LSeries5.L_E5)) 1 := by
      exact product_second_deriv hf2 hg2
    _ = Lf 1 * deriv (deriv (BSD.LSeries5.L_E5)) 1 := by
      rw [hLg0, hLg'0]
      ring
    _ = BSD.Positivity.LE_one * BSD.Positivity.Lprimeprime_E5_one := by
      rw [← hLE, ← hppE5]

/-- (1,1) 型对象消去（纠缠）：rank E(ℚ) = 1 ∧ rank E⁵(ℚ) = 1 ⟹
    L″(E/K,1) = 2·L′(E,1)·L′(E⁵,1)。 -/
theorem leibniz_11_second_object (hE1 : BSD.Positivity.zeroOrderE = 1)
    (hE5_1 : BSD.Positivity.zeroOrderE5 = 1) :
    BSD.Positivity.Lprimeprime_EK_one =
      (2 : ℝ) * BSD.Positivity.Lprime_E_one * BSD.Positivity.Lprime_E5_one := by
  rcases L_fun_structure with ⟨Lf, LKf, hEK, hf2, hg2, hK2, hppEK, hppE, hppE5,
    hpE, hpE5, hLE, hLE5⟩
  have hLE0 : BSD.Positivity.LE_one = 0 :=
    BSD.Positivity.L_value_zero_of_rank_pos (by simp [hE1])
  have hLE5_0 : BSD.Positivity.LE5_one = 0 :=
    BSD.Positivity.L_value_zero_of_rank_pos5 (by simp [hE5_1])
  have hLf0 : Lf 1 = 0 := by rw [hLE] at hLE0; exact hLE0
  have hLg0 : BSD.LSeries5.L_E5 1 = 0 := by rw [hLE5] at hLE5_0; exact hLE5_0
  calc
    BSD.Positivity.Lprimeprime_EK_one = deriv (deriv LKf) 1 := hppEK
    _ = deriv (deriv (fun s => Lf s * BSD.LSeries5.L_E5 s)) 1 := by rw [hEK]
    _ = deriv (deriv Lf) 1 * BSD.LSeries5.L_E5 1 +
        (2 : ℝ) * deriv Lf 1 * deriv (BSD.LSeries5.L_E5) 1 +
          Lf 1 * deriv (deriv (BSD.LSeries5.L_E5)) 1 := by
      exact product_second_deriv hf2 hg2
    _ = (2 : ℝ) * deriv Lf 1 * deriv (BSD.LSeries5.L_E5) 1 := by
      rw [hLg0, hLf0]
      ring
    _ = (2 : ℝ) * BSD.Positivity.Lprime_E_one * BSD.Positivity.Lprime_E5_one := by
      rw [← hpE, ← hpE5]

/-- P* 的 (2,0) 分支（经 Leibniz 真定理）：L″(E/K,1) = L″(E,1)·L(E⁵,1) > 0，
    由秩 2 分量正性 × 秩 0 分量正性（Positivity 的分量级 BSD 正性 axiom）。 -/
theorem p_star_type_20_via_leibniz (hE2 : BSD.Positivity.zeroOrderE = 2)
    (hE5_0 : BSD.Positivity.zeroOrderE5 = 0) :
    0 < BSD.Positivity.Lprimeprime_EK_one := by
  rw [leibniz_20_second_object hE2 hE5_0]
  exact mul_pos (BSD.Positivity.lprimeprime_pos_of_rank_two hE2)
    (BSD.Positivity.l_one_pos_of_rank_zero5 hE5_0)

/-- P* 的 (0,2) 分支（镜像）。 -/
theorem p_star_type_02_via_leibniz (hE0 : BSD.Positivity.zeroOrderE = 0)
    (hE5_2 : BSD.Positivity.zeroOrderE5 = 2) :
    0 < BSD.Positivity.Lprimeprime_EK_one := by
  rw [leibniz_02_second_object hE0 hE5_2]
  exact mul_pos (BSD.Positivity.l_one_pos_of_rank_zero hE0)
    (BSD.Positivity.lprimeprime_pos_of_rank_two5 hE5_2)

/-- P* 的 (1,1) 分支（纠缠）：2·L′(E,1)·L′(E⁵,1) > 0 恰为两个秩 1 分量正性的乘积——
    P* 的内容就是秩 1 BSD 正性，重述于 Leibniz 三型。 -/
theorem p_star_type_11_via_leibniz (hE1 : BSD.Positivity.zeroOrderE = 1)
    (hE5_1 : BSD.Positivity.zeroOrderE5 = 1) :
    0 < BSD.Positivity.Lprimeprime_EK_one := by
  rw [leibniz_11_second_object hE1 hE5_1]
  exact mul_pos (mul_pos (by norm_num : (2 : ℝ) > 0)
    (BSD.Positivity.lprime_pos_of_rank_one hE1))
    (BSD.Positivity.lprime_pos_of_rank_one5 hE5_1)

/-- **P* 镜像（经 Leibniz 真定理）**：解析秩恰 2 ⟹ L″(E/K,1) > 0。
    与 `BSD.Positivity.p_star` 结论一致，但 Leibniz 内容来自真定理
    （`leibniz_artin_theorem` 系），闭包不含 leibniz_artin 数值 axiom。 -/
theorem p_star_via_leibniz (h : BSD.Positivity.zeroOrderE + BSD.Positivity.zeroOrderE5 = 2) :
    0 < BSD.Positivity.Lprimeprime_EK_one := by
  rcases BSD.Positivity.type_trichotomy h with h02 | h11 | h20
  · rcases h02 with ⟨hE0, hE5_2⟩
    exact p_star_type_02_via_leibniz hE0 hE5_2
  · rcases h11 with ⟨hE1, hE5_1⟩
    exact p_star_type_11_via_leibniz hE1 hE5_1
  · rcases h20 with ⟨hE2, hE5_0⟩
    exact p_star_type_20_via_leibniz hE2 hE5_0

end

end BSD.LeibnizReduction
