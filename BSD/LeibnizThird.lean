/-
任务 8 · n=3 困难平移第一块骨架：(2,1)/(1,2) 型三阶 Leibniz 首项公式真定理化。

数学事实（纯微积分，Artin 分解 L(E/K,·) = L(E,·)·L(E⁵,·) 的三阶推广）：
  (f·g)‴(1) = f‴(1)·g(1) + 3·f″(1)·g′(1) + 3·f′(1)·g″(1) + f(1)·g‴(1)
  (2,1) 型（f(1)=f′(1)=0, g(1)=0，即 ord f = 2, ord g = 1）消去为
  (f·g)‴(1) = 3·f″(1)·g′(1) = C(3,2)·f″(1)·g′(1)          [首项系数 3]
  对称 (1,2) 型（f(1)=0, g(1)=g′(1)=0）：
  (f·g)‴(1) = 3·f′(1)·g″(1) = C(3,1)·f′(1)·g″(1)

证明路线：手工三层（一阶 → 二阶 → 三阶），v 内逐点恒等式 + 事件等价 + HasDerivAt 组合；
闭包 = 纯逻辑（propext/Classical.choice/Quot.sound），无 axiom、无公式、无 GRH。
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open scoped Topology

namespace BSD.LeibnizThird

/-- f 在 1 三阶可微：存在开邻域 v ∋ 1，f 在 v 上 C³。
Artin 分解因子 L(E,·)、L(E⁵,·) 的光滑性来源。 -/
def C3At (f : ℝ → ℝ) : Prop := ∃ v, v ∈ 𝓝 1 ∧ IsOpen v ∧ ContDiffOn ℝ 3 f v

/-- 三阶乘积求导（完整 Leibniz 公式，n=3）：(f·g)‴(1) 的展开。 -/
theorem product_third_deriv {f g : ℝ → ℝ} (hf : C3At f) (hg : C3At g) :
    deriv (deriv (deriv (fun s => f s * g s))) 1 =
      deriv (deriv (deriv f)) 1 * g 1 + (3 : ℝ) * deriv (deriv f) 1 * deriv g 1
        + (3 : ℝ) * deriv f 1 * deriv (deriv g) 1 + f 1 * deriv (deriv (deriv g)) 1 := by
  rcases hf with ⟨vf, hvf_nhds, hvf_open, hfv⟩
  rcases hg with ⟨vg, hvg_nhds, hvg_open, hgv⟩
  let v : Set ℝ := vf ∩ vg
  have hv_nhds : v ∈ 𝓝 1 := Filter.inter_mem hvf_nhds hvg_nhds
  have hv_open : IsOpen v := hvf_open.inter hvg_open
  have h1v : 1 ∈ v := mem_of_mem_nhds hv_nhds
  have hfv' : ContDiffOn ℝ 3 f v := hfv.mono (by intro s hs; exact hs.1)
  have hgv' : ContDiffOn ℝ 3 g v := hgv.mono (by intro s hs; exact hs.2)
  -- C³ 分层（v 开，succ 分解）：
  --   f、g 可微；A := deriv f、B := deriv g 可微；deriv A、deriv B 可微
  have hf_diff : DifferentiableOn ℝ f v :=
    hfv'.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hg_diff : DifferentiableOn ℝ g v :=
    hgv'.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hfA2 : ContDiffOn ℝ 2 (deriv f) v :=
    (contDiffOn_succ_iff_deriv_of_isOpen (s := v) (n := (2 : WithTop ℕ∞)) (f := f) hv_open).mp hfv' |>.2.2
  have hgB2 : ContDiffOn ℝ 2 (deriv g) v :=
    (contDiffOn_succ_iff_deriv_of_isOpen (s := v) (n := (2 : WithTop ℕ∞)) (f := g) hv_open).mp hgv' |>.2.2
  have hA_diff : DifferentiableOn ℝ (deriv f) v :=
    hfA2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hB_diff : DifferentiableOn ℝ (deriv g) v :=
    hgB2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hfA1 : ContDiffOn ℝ 1 (deriv (deriv f)) v :=
    (contDiffOn_succ_iff_deriv_of_isOpen (s := v) (n := (1 : WithTop ℕ∞)) (f := deriv f) hv_open).mp hfA2 |>.2.2
  have hgB1 : ContDiffOn ℝ 1 (deriv (deriv g)) v :=
    (contDiffOn_succ_iff_deriv_of_isOpen (s := v) (n := (1 : WithTop ℕ∞)) (f := deriv g) hv_open).mp hgB2 |>.2.2
  have hdA_diff : DifferentiableOn ℝ (deriv (deriv f)) v :=
    hfA1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hdB_diff : DifferentiableOn ℝ (deriv (deriv g)) v :=
    hgB1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  -- 逐点可微 at s ∈ v（DifferentiableOn 在 v 上是 Within 型，由 v 开提升到 At）
  have hf_diffAt : ∀ s ∈ v, DifferentiableAt ℝ f s := fun s hs =>
    (hf_diff s hs).differentiableAt (hv_open.mem_nhds hs)
  have hg_diffAt : ∀ s ∈ v, DifferentiableAt ℝ g s := fun s hs =>
    (hg_diff s hs).differentiableAt (hv_open.mem_nhds hs)
  have hA_diffAt : ∀ s ∈ v, DifferentiableAt ℝ (deriv f) s := fun s hs =>
    (hA_diff s hs).differentiableAt (hv_open.mem_nhds hs)
  have hB_diffAt : ∀ s ∈ v, DifferentiableAt ℝ (deriv g) s := fun s hs =>
    (hB_diff s hs).differentiableAt (hv_open.mem_nhds hs)
  have hdA_diffAt : ∀ s ∈ v, DifferentiableAt ℝ (deriv (deriv f)) s := fun s hs =>
    (hdA_diff s hs).differentiableAt (hv_open.mem_nhds hs)
  have hdB_diffAt : ∀ s ∈ v, DifferentiableAt ℝ (deriv (deriv g)) s := fun s hs =>
    (hdB_diff s hs).differentiableAt (hv_open.mem_nhds hs)
  -- 第一层：v 内逐点 (f·g)′ = f′·g + f·g′
  have h1 : ∀ s ∈ v, deriv (fun t => f t * g t) s = deriv f s * g s + f s * deriv g s := by
    intro s hs
    exact deriv_mul (hf_diffAt s hs) (hg_diffAt s hs)
  -- 第二层：v 内逐点 (f′·g + f·g′)′ = f″·g + 2·f′·g′ + f·g″
  have h2 : ∀ s ∈ v,
      deriv (fun t => deriv f t * g t + f t * deriv g t) s =
        deriv (deriv f) s * g s + deriv f s * deriv g s
          + deriv f s * deriv g s + f s * deriv (deriv g) s := by
    intro s hs
    have hder_fg : deriv (fun t => deriv f t * g t) s =
        deriv (deriv f) s * g s + deriv f s * deriv g s :=
      deriv_mul (hA_diffAt s hs) (hg_diffAt s hs)
    have hder_fg' : deriv (fun t => f t * deriv g t) s =
        deriv f s * deriv g s + f s * deriv (deriv g) s :=
      deriv_mul (hf_diffAt s hs) (hB_diffAt s hs)
    calc
      deriv (fun t => deriv f t * g t + f t * deriv g t) s
          = deriv (fun t => deriv f t * g t) s + deriv (fun t => f t * deriv g t) s := by
            apply deriv_add
            · exact DifferentiableAt.mul (hA_diffAt s hs) (hg_diffAt s hs)
            · exact DifferentiableAt.mul (hf_diffAt s hs) (hB_diffAt s hs)
      _ = deriv (deriv f) s * g s + deriv f s * deriv g s
            + deriv f s * deriv g s + f s * deriv (deriv g) s := by
            rw [hder_fg, hder_fg']
            ring
  -- 第三层：v 内逐点 (f·g)″ = f″·g + 2·f′·g′ + f·g″（由第一层的局部性推第二层导数）
  have h2p : ∀ s ∈ v,
      deriv (deriv (fun t => f t * g t)) s =
        deriv (deriv f) s * g s + deriv f s * deriv g s
          + deriv f s * deriv g s + f s * deriv (deriv g) s := by
    intro s hs
    calc
      deriv (deriv (fun t => f t * g t)) s
          = deriv (fun t => deriv (fun u => f u * g u) t) s := rfl
      _ = deriv (fun t => deriv f t * g t + f t * deriv g t) s := by
            have hloc : (fun t => deriv (fun u => f u * g u) t) =ᶠ[𝓝 s]
                (fun t => deriv f t * g t + f t * deriv g t) := by
              filter_upwards [hv_open.mem_nhds hs] with t ht
              exact h1 t ht
            exact hloc.deriv_eq
      _ = deriv (deriv f) s * g s + deriv f s * deriv g s
            + deriv f s * deriv g s + f s * deriv (deriv g) s := h2 s hs
  -- 事件等价（𝓝 1）：
  have hevT : (fun s => deriv (deriv (fun t => f t * g t)) s) =ᶠ[𝓝 1]
      (fun s => deriv (deriv f) s * g s + deriv f s * deriv g s
        + deriv f s * deriv g s + f s * deriv (deriv g) s) := by
    filter_upwards [hv_nhds] with s hs
    exact h2p s hs
  -- HasDerivAt 链（点 1）：
  have hf1 : HasDerivAt f (deriv f 1) 1 := (hf_diffAt 1 h1v).hasDerivAt
  have hg1 : HasDerivAt g (deriv g 1) 1 := (hg_diffAt 1 h1v).hasDerivAt
  have hA1 : HasDerivAt (deriv f) (deriv (deriv f) 1) 1 := (hA_diffAt 1 h1v).hasDerivAt
  have hB1 : HasDerivAt (deriv g) (deriv (deriv g) 1) 1 := (hB_diffAt 1 h1v).hasDerivAt
  have hdA1 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) 1) 1 :=
    (hdA_diffAt 1 h1v).hasDerivAt
  have hdB1 : HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) 1) 1 :=
    (hdB_diffAt 1 h1v).hasDerivAt
  -- 组合：V3 = f‴(1)·g(1) + 3·f″(1)·g′(1) + 3·f′(1)·g″(1) + f(1)·g‴(1)
  let V3 : ℝ := deriv (deriv (deriv f)) 1 * g 1 + (3 : ℝ) * deriv (deriv f) 1 * deriv g 1
      + (3 : ℝ) * deriv f 1 * deriv (deriv g) 1 + f 1 * deriv (deriv (deriv g)) 1
  have hdAg : HasDerivAt (fun s => deriv (deriv f) s * g s)
      (deriv (deriv (deriv f)) 1 * g 1 + deriv (deriv f) 1 * deriv g 1) 1 := hdA1.mul hg1
  have hAB : HasDerivAt (fun s => deriv f s * deriv g s)
      (deriv (deriv f) 1 * deriv g 1 + deriv f 1 * deriv (deriv g) 1) 1 := hA1.mul hB1
  have hfdB : HasDerivAt (fun s => f s * deriv (deriv g) s)
      (deriv f 1 * deriv (deriv g) 1 + f 1 * deriv (deriv (deriv g)) 1) 1 := hf1.mul hdB1
  have hsum3 : HasDerivAt
      (fun s => deriv (deriv f) s * g s + deriv f s * deriv g s
        + deriv f s * deriv g s + f s * deriv (deriv g) s)
      ((deriv (deriv (deriv f)) 1 * g 1 + deriv (deriv f) 1 * deriv g 1)
        + (deriv (deriv f) 1 * deriv g 1 + deriv f 1 * deriv (deriv g) 1)
        + (deriv (deriv f) 1 * deriv g 1 + deriv f 1 * deriv (deriv g) 1)
        + (deriv f 1 * deriv (deriv g) 1 + f 1 * deriv (deriv (deriv g)) 1)) 1 := by
    have h1a : HasDerivAt (fun s => deriv (deriv f) s * g s + deriv f s * deriv g s)
        ((deriv (deriv (deriv f)) 1 * g 1 + deriv (deriv f) 1 * deriv g 1)
          + (deriv (deriv f) 1 * deriv g 1 + deriv f 1 * deriv (deriv g) 1)) 1 := hdAg.add hAB
    have h1b : HasDerivAt (fun s => deriv (deriv f) s * g s + deriv f s * deriv g s
          + deriv f s * deriv g s)
        (((deriv (deriv (deriv f)) 1 * g 1 + deriv (deriv f) 1 * deriv g 1)
          + (deriv (deriv f) 1 * deriv g 1 + deriv f 1 * deriv (deriv g) 1))
          + (deriv (deriv f) 1 * deriv g 1 + deriv f 1 * deriv (deriv g) 1)) 1 := h1a.add hAB
    exact h1b.add hfdB
  have hsum3' : HasDerivAt
      (fun s => deriv (deriv f) s * g s + deriv f s * deriv g s
        + deriv f s * deriv g s + f s * deriv (deriv g) s) V3 1 := by
    convert hsum3 using 1
    ring
  have hT : HasDerivAt (fun s => deriv (deriv (fun t => f t * g t)) s) V3 1 :=
    hsum3'.congr_of_eventuallyEq hevT
  calc
    deriv (deriv (deriv (fun s => f s * g s))) 1
        = deriv (fun s => deriv (deriv (fun t => f t * g t)) s) 1 := rfl
    _ = V3 := hT.deriv
    _ = deriv (deriv (deriv f)) 1 * g 1 + (3 : ℝ) * deriv (deriv f) 1 * deriv g 1
          + (3 : ℝ) * deriv f 1 * deriv (deriv g) 1 + f 1 * deriv (deriv (deriv g)) 1 := by
          simp [V3]

/-- (2,1) 型三阶 Leibniz 首项公式：ord f = 2（f(1)=f′(1)=0）、ord g = 1（g(1)=0）
⟹ (f·g)‴(1) = C(3,2)·f″(1)·g′(1) = 3·f″(1)·g′(1)。 -/
theorem leibniz_21_third {f g : ℝ → ℝ} (hf : C3At f) (hg : C3At g)
    (hf0 : f 1 = 0) (hf1 : deriv f 1 = 0) (hg0 : g 1 = 0) :
    deriv (deriv (deriv (fun s => f s * g s))) 1 =
      (3 : ℝ) * deriv (deriv f) 1 * deriv g 1 := by
  rw [product_third_deriv hf hg, hf0, hf1, hg0]
  ring

/-- (1,2) 型对称：ord f = 1（f(1)=0）、ord g = 2（g(1)=g′(1)=0）
⟹ (f·g)‴(1) = C(3,1)·f′(1)·g″(1) = 3·f′(1)·g″(1)。 -/
theorem leibniz_12_third {f g : ℝ → ℝ} (hf : C3At f) (hg : C3At g)
    (hf0 : f 1 = 0) (hg0 : g 1 = 0) (hg1 : deriv g 1 = 0) :
    deriv (deriv (deriv (fun s => f s * g s))) 1 =
      (3 : ℝ) * deriv f 1 * deriv (deriv g) 1 := by
  rw [product_third_deriv hf hg, hf0, hg0, hg1]
  ring

/-- (2,1) 型非零传播：f″(1) ≠ 0 ∧ g′(1) ≠ 0 ⟹ (f·g)‴(1) ≠ 0。 -/
theorem leibniz_21_third_ne_zero {f g : ℝ → ℝ} (hf : C3At f) (hg : C3At g)
    (hf0 : f 1 = 0) (hf1 : deriv f 1 = 0) (hg0 : g 1 = 0)
    (hfpp : deriv (deriv f) 1 ≠ 0) (hgp : deriv g 1 ≠ 0) :
    deriv (deriv (deriv (fun s => f s * g s))) 1 ≠ 0 := by
  rw [leibniz_21_third hf hg hf0 hf1 hg0]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hfpp) hgp

/-- (1,2) 型非零传播：f′(1) ≠ 0 ∧ g″(1) ≠ 0 ⟹ (f·g)‴(1) ≠ 0。 -/
theorem leibniz_12_third_ne_zero {f g : ℝ → ℝ} (hf : C3At f) (hg : C3At g)
    (hf0 : f 1 = 0) (hg0 : g 1 = 0) (hg1 : deriv g 1 = 0)
    (hfp : deriv f 1 ≠ 0) (hgpp : deriv (deriv g) 1 ≠ 0) :
    deriv (deriv (deriv (fun s => f s * g s))) 1 ≠ 0 := by
  rw [leibniz_12_third hf hg hf0 hg0 hg1]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hfp) hgpp

end BSD.LeibnizThird
