#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# 读取文件
file_path = r"C:\proj2\OrderPreservingBijection\stage_4.lean"

with open(file_path, 'r', encoding='utf-8') as f:
    content = f.read()

# 用正则表达式替换
import re

pattern = r'theorem shimuraLift_linear \(a : ℂ\) \(f : L2ManifoldX\) :.*?exact h_main'
replacement = """theorem shimuraLift_linear (a : ℂ) (f : L2ManifoldX) :
    shimuraLift (a • f) = a • shimuraLift f := by sorry"""

content = re.sub(pattern, replacement, content, flags=re.DOTALL)

# 写回文件
with open(file_path, 'w', encoding='utf-8') as f:
    f.write(content)

print("Restored!")
