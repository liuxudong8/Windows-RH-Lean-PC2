# -*- coding: utf-8 -*-
"""解析 build_fresh_20261002.txt 中 #print axioms 输出：
格式: info: <file>:<line>:0: '<name>' depends on axioms: [propext, sorryAx, ...]
统计: 总声明数 / 含 sorryAx / 不含 sorryAx（仅标准公理）"""
import re, io

LOG = r'C:\proj2\build_axiom_20261002.txt'
TEXT = io.open(LOG, encoding='utf-8', errors='replace').read()

pattern = re.compile(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.S)
decls = {}
for m in pattern.finditer(TEXT):
    name = m.group(1)
    axioms = [a.strip() for a in m.group(2).replace('\n', ' ').split(',') if a.strip()]
    decls[name] = axioms

std = {'propext', 'Classical.choice', 'Quot.sound', 'funext', 'Classical.choice'}  # 标准/无争议公理

with_sorry = {n: ax for n, ax in decls.items() if 'sorryAx' in ax}
without_sorry = {n: ax for n, ax in decls.items() if 'sorryAx' not in ax}

print('== 日志中记录到 #print axioms 的声明总数: %d' % len(decls))
print('== 依赖 sorryAx（有未完成证明泄漏）: %d' % len(with_sorry))
for n, ax in sorted(with_sorry.items()):
    print('   %-75s %s' % (n, ', '.join(ax)))
print('== 不含 sorryAx 的声明: %d' % len(without_sorry))
for n, ax in sorted(without_sorry.items()):
    print('   %-75s %s' % (n, ', '.join(ax)))
