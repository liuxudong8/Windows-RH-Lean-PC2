#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# 读取文件
file_path = r"C:\proj2\OrderPreservingBijection\stage_4.lean"

with open(file_path, 'r', encoding='utf-8') as f:
    content = f.read()

# 用正则表达式替换
import re

pattern = r'-- 如果 f ≠ 0，那么存在某个 z 使得 f.toFun z ≠ 0.*?exact h5'
replacement = """theorem eigenfunction_cancellation (n : ℕ) (a b : ℂ) :
    a • threeManifoldEigenfunction n = b • threeManifoldEigenfunction n → a = b := by sorry"""

content = re.sub(pattern, replacement, content, flags=re.DOTALL)

# 写回文件
with open(file_path, 'w', encoding='utf-8') as f:
    f.write(content)

print("Restored!")
