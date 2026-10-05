import shutil

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

new_lemmas = '''
lemma sum_quadratic_geometric_formula (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) = 12 - 2 * ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [pow_succ] <;> field_simp <;> ring

lemma summable_quadratic_over_geometric : Summable (fun (k : ℕ) => ((k : ℝ) + 1)^2 / (2 : ℝ)^k) := by
  have h_nonneg : ∀ (k : ℕ), 0 ≤ ((k : ℝ) + 1)^2 / (2 : ℝ)^k := by intro k; positivity
  have h_bounded : ∀ (n : ℕ), ∑ i ∈ Finset.range n, (((i : ℝ) + 1)^2 / (2 : ℝ)^i) ≤ 12 := by
    intro n
    have h_formula := sum_quadratic_geometric_formula n
    rw [h_formula]
    have h_pos : 0 ≤ 2 * ((n : ℝ)^2 + 4 * (n : ℝ) + 6) / (2 : ℝ)^n := by positivity
    linarith
  exact summable_of_sum_range_le h_nonneg h_bounded

'''

marker = 'lemma layer_sum_bound'
if marker in content:
    # 在 layer_sum_bound 之前插入（实际上应该在之后，但之前也行，因为它们不依赖）
    # 找到 layer_sum_bound 的结束位置，在其后插入
    # 简单起见，在 "-- === 基础设施结束 ===" 之前插入
    end_marker = '\n-- === 基础设施结束 ==='
    if end_marker in content:
        content = content.replace(end_marker, new_lemmas + '\n-- === 基础设施结束 ===')
        print("插入成功")
    else:
        print("未找到结束标记")
else:
    print("未找到 layer_sum_bound")

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("文件已更新")
