#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# 读取文件
file_path = r"C:\proj2\OrderPreservingBijection\stage_4.lean"

with open(file_path, 'r', encoding='utf-8') as f:
    content = f.read()

# 旧的证明
old = """  have h8 : a = b := by
    have h9 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := h7
    have h10 : a = b := by
      exact?
    exact h10
  exact h8"""

# 新的证明
new = """  have h8 : a = b := by
    have h9 : a * (threeManifoldEigenfunction n).toFun z = b * (threeManifoldEigenfunction n).toFun z := h7
    have h10 : a = b := by
      calc
        a = (a * (threeManifoldEigenfunction n).toFun z) / (threeManifoldEigenfunction n).toFun z := by
          field_simp [hz] <;> ring
        _ = (b * (threeManifoldEigenfunction n).toFun z) / (threeManifoldEigenfunction n).toFun z := by rw [h9]
        _ = b := by field_simp [hz] <;> ring
    exact h10
  exact h8"""

# 替换
content = content.replace(old, new)

# 写回文件
with open(file_path, 'w', encoding='utf-8') as f:
    f.write(content)

print("Modified!")
