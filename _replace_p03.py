# -*- coding: utf-8 -*-
"""P0.3: 替换 stage_4.lean 中枚举版 zero_weighted_series_summable 与两个 admit，
为 farZeroSubtype 真证版（vanishing 判据 + 几何分层）。"""
import io

P = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
src = io.open(P, encoding='utf-8').read()
lines = src.split('\n')

si = next(i for i, l in enumerate(lines)
          if l.strip().startswith('theorem zero_weighted_series_summable :'))
# 区间内最后一个裸 admit 行（farZero_weighted_tail_small 的）
ei = None
for i in range(si, min(si + 240, len(lines))):
    if lines[i].strip() == 'admit':
        ei = i
assert ei is not None, 'tail admit not found'
print('replacing lines', si + 1, '..', ei + 1, '(', ei - si + 1, 'lines )')

new_block = r'''/-- P0.3（2026-10-02）：far 零点加权和（分母 |Im|²）可和——真证，替代原枚举版。
    数学依据：零点密度估计（zero_counting_estimate）+ 重数对数增长（zero_multiplicity_log_growth）
    + |Im| 几何分层（层有限由投影单射 + 零点带有限直接推出，不再依赖 :49 枚举）。
    证明结构：summable_iff_vanishing_norm（ℝ 完备）——对任意 ε，取
    s₀ = small ∪ (∪_{k ≤ K} layer k)（K 使几何尾 ∑'_{m > K} G m < ε/2），
    任意与 s₀ 不交的有限集 t 的加权和 ≤ 几何尾 < ε。 -/
theorem farZero_weighted_summable :
    Summable (fun ρ' : farZeroSubtype => (zeroMultiplicity ρ'.1 : ℝ) / |ρ'.1.im| ^ 2) := by
  let w : farZeroSubtype → ℝ := fun ρ' => (zeroMultiplicity ρ'.1 : ℝ) / |ρ'.1.im| ^ 2
  have h_w_nonneg : ∀ ρ', 0 ≤ w ρ' := by
    intro ρ'; dsimp [w]; apply div_nonneg <;> positivity
  rw [summable_iff_vanishing_norm]
  intro ε hε
  let ε' := ε / 2
  have hε' : 0 < ε' := by positivity
  rcases zero_counting_estimate with ⟨C1, hC1_pos, hC1⟩
  rcases zero_multiplicity_log_growth with ⟨C2, hC2_pos, hC2⟩
  let small : Set farZeroSubtype := {ρ' | |ρ'.1.im| < 1}
  let layer : ℕ → Set farZeroSubtype := fun k => {ρ' | (2^k : ℝ) ≤ |ρ'.1.im| ∧ |ρ'.1.im| < (2^(k+1) : ℝ)}
  have h_small_fin : small.Finite := small_finite
  have h_layer_fin : ∀ k, (layer k).Finite := by
    intro k
    let T := (2^(k+1) : ℝ)
    have hT_pos : 0 < T := by positivity
    let S_up : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}
    have h_up_fin : S_up.Finite := finite_of_encard_le (hC1 T hT_pos)
    let S_low : Set ℂ := {s | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0}
    have h_low_fin : S_low.Finite := by
      have h_conj_map : S_low = (fun s : ℂ => star s) '' S_up := by
        ext s
        simp only [S_up, S_low, Set.mem_image]
        constructor
        · intro h
          refine ⟨star s, ?_, by simp⟩
          have h_zeta : _root_.riemannZeta (star s) = 0 := by rw [riemannZeta_conj, h.1]; simp
          have h_im1 : 0 ≤ (star s).im := by simp [Complex.ext_iff] at h ⊢ <;> linarith
          have h_im2 : (star s).im ≤ T := by simp [Complex.ext_iff] at h ⊢ <;> linarith
          exact ⟨h_zeta, h.2.1, h.2.2.1, h_im1, h_im2⟩
        · rintro ⟨t, ht, rfl⟩
          have h_zeta : _root_.riemannZeta (star t) = 0 := by rw [riemannZeta_conj, ht.1]; simp
          have h_im1 : -T ≤ (star t).im := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
          have h_im2 : (star t).im ≤ 0 := by simp [Complex.ext_iff] at ht ⊢ <;> linarith
          exact ⟨h_zeta, ht.2.1, ht.2.2.1, h_im1, h_im2⟩
      rw [h_conj_map]; exact h_up_fin.image _
    have h_band : {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T} ⊆ S_up ∪ S_low := by
      intro s hs
      have h2 : |s.im| < T := hs.2.2.2
      have h2' : -T < s.im ∧ s.im < T := abs_lt.mp h2
      by_cases h3 : 0 ≤ s.im
      · left; exact ⟨hs.1, hs.2.1, hs.2.2.1, h3, by linarith⟩
      · right
        have h4 : s.im < 0 := by linarith
        have h5 : -T ≤ s.im := by linarith
        have h6 : s.im ≤ 0 := by linarith
        have h_goal : _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ -T ≤ s.im ∧ s.im ≤ 0 :=
          ⟨hs.1, hs.2.1, hs.2.2.1, h5, h6⟩
        simpa [S_low] using h_goal
    have h_band_fin : ({s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T}).Finite :=
      (h_up_fin.union h_low_fin).subset h_band
    have h_img_subset : (fun ρ' : farZeroSubtype => ρ'.1) '' (layer k) ⊆
        {s : ℂ | _root_.riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| < T} := by
      intro s hs
      rcases hs with ⟨ρ', hρ', rfl⟩
      have hz' : _root_.riemannZeta ρ'.1 = 0 := ρ'.2.1
      have hre1' : 0 < ρ'.1.re := ρ'.2.2.1
      have hre2' : ρ'.1.re < 1 := ρ'.2.2.2.1
      have him' : |ρ'.1.im| < T := by
        have h : |ρ'.1.im| < (2^(k+1) : ℝ) := hρ'.2
        rw [show (2^(k+1) : ℝ) = T by rfl]
        exact h
      exact ⟨hz', hre1', hre2', him'⟩
    have h_img_fin : ((fun ρ' : farZeroSubtype => ρ'.1) '' (layer k)).Finite := h_band_fin.subset h_img_subset
    have h_inj : Set.InjOn (fun ρ' : farZeroSubtype => ρ'.1) (layer k) := by
      intro ρ' _ ρ'' _ h
      exact Subtype.ext h
    exact Set.Finite.of_finite_image h_img_fin h_inj
  let C := (16 * C1 + 2) * (C2 * 4 + 1)
  have h_layer_sum : ∀ (k : ℕ), ∑ ρ' ∈ (h_layer_fin k).toFinset, w ρ' ≤ C * ((k : ℝ) + 1)^2 / (2^k : ℝ) := by
    intro k
    have h := layer_sum_bound2 C1 C2 hC1_pos hC2_pos hC1 hC2 k (h_layer_fin k)
    simpa [w, C, sq_abs] using h
  let G : ℕ → ℝ := fun k => C * ((k : ℝ) + 1)^2 / (2^k : ℝ)
  have hG_nonneg : ∀ k, 0 ≤ G k := by intro k; dsimp [G]; positivity
  have hG_summable : Summable G := by
    have h : Summable (fun k : ℕ => ((k : ℝ) + 1)^2 / (2^k : ℝ)) := summable_quadratic_over_geometric
    have h_eq : (fun (k : ℕ) => C * (((k : ℝ) + 1)^2 / (2^k : ℝ))) = (fun (k : ℕ) => C * ((k : ℝ) + 1)^2 / (2^k : ℝ)) := by
      funext k
      field_simp
      <;> ring
    rw [← h_eq]
    exact Summable.mul_left C h
  have hK_exists : ∃ K : ℕ, ∑' m : ℕ, (if K < m then G m else 0) < ε' := by
    have h_tend : Tendsto (fun s : Finset ℕ => ∑' (m : {m // m ∉ s}), G m) atTop (𝓝 0) :=
      tendsto_tsum_compl_atTop_zero G
    have h_event : ∀ᶠ s : Finset ℕ in atTop, (∑' (m : {m // m ∉ s}), G m) < ε' :=
      (tendsto_order.mp h_tend).2 ε' hε'
    rcases eventually_atTop.mp h_event with ⟨N, hN⟩
    let K := N.sup id
    refine ⟨K, ?_⟩
    have h_eq_N : ∑' m : ℕ, (if m ∉ N then G m else 0) = ∑' (m : {m // m ∉ N}), G m := by
      rw [tsum_subtype]
      simp
    have h_le_indic : (fun m : ℕ => if K < m then G m else 0) ≤ (fun m : ℕ => if m ∉ N then G m else 0) := by
      intro m
      by_cases h : K < m
      · have hnot : m ∉ N := by
          intro hm
          have hle : m ≤ N.sup id := by
            simpa using (Finset.le_sup hm : id m ≤ N.sup id)
          linarith
        simp [h, hnot]
      · simp [h]
    have h_tail_summable_N : Summable (fun m : ℕ => if m ∉ N then G m else 0) := by
      refine Summable.of_nonneg_of_le hG_nonneg ?_ hG_summable
      intro m; by_cases h : m ∉ N <;> simp [h]
    have h_tail_summable_K : Summable (fun m : ℕ => if K < m then G m else 0) := by
      refine Summable.of_nonneg_of_le hG_nonneg ?_ hG_summable
      intro m; by_cases h : K < m <;> simp [h]
    have h_ineq : ∑' m : ℕ, (if K < m then G m else 0) ≤ ∑' m : ℕ, (if m ∉ N then G m else 0) :=
      Summable.tsum_le_tsum h_le_indic h_tail_summable_K h_tail_summable_N
    calc
      ∑' m : ℕ, (if K < m then G m else 0) ≤ ∑' m : ℕ, (if m ∉ N then G m else 0) := h_ineq
      _ = ∑' (m : {m // m ∉ N}), G m := h_eq_N.symm
      _ < ε' := hN N (subset_rfl)
  rcases hK_exists with ⟨K, hK_tail⟩
  let s₀ : Finset farZeroSubtype := h_small_fin.toFinset ∪
    Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset)
  refine ⟨s₀, ?_⟩
  intro t ht
  let idx : farZeroSubtype → ℕ := fun ρ' =>
    if h : 1 ≤ |ρ'.1.im| then (exists_layer_index |ρ'.1.im| h).choose else 0
  have h_t_idx : ∀ i ∈ t, K < idx i ∧ i ∈ layer (idx i) := by
    intro i hi
    have h_not_union : i ∉ h_small_fin.toFinset ∪ (Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset)) :=
      (Finset.disjoint_left.mp ht) hi
    have h_not_small : i ∉ h_small_fin.toFinset := by
      intro hs; exact h_not_union (Finset.mem_union_left _ hs)
    have h_not_small_set : ¬ i ∈ small := by
      intro hs
      exact h_not_small ((Set.Finite.mem_toFinset h_small_fin).mpr hs)
    have hge : 1 ≤ |i.1.im| := by
      by_contra h
      have hlt : |i.1.im| < 1 := by linarith
      exact h_not_small_set (by simpa [small] using hlt)
    have h_layer_mem : i ∈ layer (idx i) := by
      have hspec := (exists_layer_index |i.1.im| hge).choose_spec
      dsimp [idx]
      simp [hge]
      exact hspec
    have h_not_layer_le : ∀ k ≤ K, i ∉ (h_layer_fin k).toFinset := by
      intro k hk
      intro hmem
      have h_in_bi : i ∈ Finset.biUnion (Finset.range (K + 1)) (fun k => (h_layer_fin k).toFinset) :=
        Finset.mem_biUnion.mpr ⟨k, by simp [Finset.mem_range]; omega, hmem⟩
      exact h_not_union (Finset.mem_union_right _ h_in_bi)
    have hK_lt : K < idx i := by
      by_contra h
      have hle : idx i ≤ K := by omega
      have him_mem : i ∈ (h_layer_fin (idx i)).toFinset :=
        (Set.Finite.mem_toFinset (h_layer_fin (idx i))).mpr h_layer_mem
      exact (h_not_layer_le (idx i) hle) him_mem
    exact ⟨hK_lt, h_layer_mem⟩
  let Ks : Finset ℕ := t.image idx
  have h_sum_decomp : (∑ k ∈ Ks, ∑ i ∈ t, (if idx i = k then w i else 0)) = ∑ i ∈ t, w i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have h_mem : idx i ∈ Ks := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [Finset.sum_eq_single (idx i)]
    · simp
    · intro b hb hbne
      simp [hbne.symm]
    · intro hnot
      exact (hnot h_mem).elim
  have h_bound1 : (∑ k ∈ Ks, ∑ i ∈ t, (if idx i = k then w i else 0)) ≤
      ∑ k ∈ Ks, ∑ i ∈ (h_layer_fin k).toFinset, w i := by
    apply Finset.sum_le_sum
    intro k hk
    have h_sub : t.filter (fun i => idx i = k) ⊆ (h_layer_fin k).toFinset := by
      intro i hi
      have hik : idx i = k := (Finset.mem_filter.mp hi).2
      have hit : i ∈ t := (Finset.mem_filter.mp hi).1
      have hli : i ∈ layer (idx i) := (h_t_idx i hit).2
      have hmem : i ∈ layer k := by
        simpa [hik] using hli
      exact (Set.Finite.mem_toFinset (h_layer_fin k)).mpr hmem
    calc
      ∑ i ∈ t, (if idx i = k then w i else 0)
        = ∑ i ∈ t.filter (fun i => idx i = k), w i := by rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ (h_layer_fin k).toFinset, w i :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun i _ _ => h_w_nonneg i)
  have h_bound2 : (∑ k ∈ Ks, ∑ i ∈ (h_layer_fin k).toFinset, w i) ≤ ∑ k ∈ Ks, G k := by
    apply Finset.sum_le_sum
    intro k hk
    exact h_layer_sum k
  have h_bound3 : ∑ k ∈ Ks, G k ≤ ∑' m : ℕ, (if K < m then G m else 0) := by
    have h_sub : ∀ k ∈ Ks, K < k := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
      exact (h_t_idx i hi).1
    have h_eq : (∑ k ∈ Ks, G k) = ∑ k ∈ Ks, (if K < k then G k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hlt : K < k := h_sub k hk
      simp [hlt]
    have h_tail_summable_K : Summable (fun m : ℕ => if K < m then G m else 0) := by
      refine Summable.of_nonneg_of_le hG_nonneg ?_ hG_summable
      intro m; by_cases h : K < m <;> simp [h]
    rw [h_eq]
    exact Summable.sum_le_tsum Ks (by intro m hm; by_cases h : K < m <;> simp [h]) h_tail_summable_K
  have h_sum_lt : (∑ i ∈ t, w i) < ε' := by
    calc
      (∑ i ∈ t, w i) = (∑ k ∈ Ks, ∑ i ∈ t, (if idx i = k then w i else 0)) := h_sum_decomp.symm
      _ ≤ ∑ k ∈ Ks, ∑ i ∈ (h_layer_fin k).toFinset, w i := h_bound1
      _ ≤ ∑ k ∈ Ks, G k := h_bound2
      _ ≤ ∑' m : ℕ, (if K < m then G m else 0) := h_bound3
      _ < ε' := hK_tail
  have h_pos_sum : 0 ≤ ∑ i ∈ t, w i := Finset.sum_nonneg (by intro i hi; exact h_w_nonneg i)
  have h_abs : |∑ i ∈ t, w i| < ε := by
    rw [abs_of_nonneg h_pos_sum]
    linarith
  exact h_abs

/-- P0.3（2026-10-02）：围道外加权和的"有限余项可任意小"——真证，替代原 admit。
    由 tendsto_tsum_compl_atTop_zero（有限集补集上的 tsum 趋于 0）直接给出：
    存在有限集 F，使 F 外的加权余项 < threshold。 -/
theorem farZero_weighted_tail_small (threshold : ℝ) (hthr : 0 < threshold) :
    ∃ F : Finset farZeroSubtype,
      ∑' ρ' : farZeroSubtype, (if ρ' ∈ F then (0 : ℝ) else
        (zeroMultiplicity ρ'.1 : ℝ) / |ρ'.1.im| ^ 2) < threshold := by
  let w : farZeroSubtype → ℝ := fun ρ' => (zeroMultiplicity ρ'.1 : ℝ) / |ρ'.1.im| ^ 2
  have h_tend : Tendsto (fun s : Finset farZeroSubtype => ∑' (a : {a // a ∉ s}), w a) atTop (𝓝 0) :=
    tendsto_tsum_compl_atTop_zero w
  have h_event : ∀ᶠ s : Finset farZeroSubtype in atTop, (∑' (a : {a // a ∉ s}), w a) < threshold :=
    (tendsto_order.mp h_tend).2 threshold hthr
  rcases eventually_atTop.mp h_event with ⟨F, hF⟩
  have hF_self : ∑' (a : {a // a ∉ F}), w a < threshold := hF F (subset_rfl)
  refine ⟨F, ?_⟩
  have h_eq : (∑' ρ' : farZeroSubtype, (if ρ' ∈ F then (0 : ℝ) else w ρ')) =
      ∑' (a : {a // a ∉ F}), w a := by
    rw [tsum_subtype]
    apply tsum_congr
    intro ρ'
    by_cases h : ρ' ∈ F <;> simp [h]
  rw [h_eq]
  exact hF_self'''
lines[si:ei + 1] = [new_block]
io.open(P, 'w', encoding='utf-8', newline='').write('\n'.join(lines))
print('done; new file lines:', len(lines))
