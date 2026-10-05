# -*- coding: utf-8 -*-
"""回溯每个 sorry/admit 所属的最近声明（theorem/lemma/def/example/axiom）。"""
import os, re

ROOT = r'C:\proj2\OrderPreservingBijection'
decl_re = re.compile(r'^\s*(theorem|lemma|def|example|axiom|noncomputable\s+(?:theorem|lemma|def))\s+([A-Za-z_][A-Za-z0-9_\.]*)')
sorry_re = re.compile(r'\b(sorry|admit)\b')

def strip_comments(lines):
    out, in_block = [], False
    for s in lines:
        res, i = '', 0
        while i < len(s):
            if in_block:
                j = s.find('-/', i)
                if j == -1: i = len(s)
                else: in_block, i = False, j + 2
            else:
                j, k = s.find('/-', i), s.find('--', i)
                if j == -1 and k == -1: res, i = res + s[i:], len(s)
                elif j != -1 and (k == -1 or j < k): res, in_block, i = res + s[i:j], True, j + 2
                else: res, i = res + s[i:k], len(s)
        out.append(res)
    return out

files = []
for dp, _, fns in os.walk(ROOT):
    for fn in fns:
        if fn.endswith('.lean') and '.bak' not in fn and not fn.startswith('test_'):
            files.append(os.path.join(dp, fn))
files.sort()

report = []
for fp in files:
    with open(fp, encoding='utf-8', errors='replace') as f:
        code = strip_comments(f.read().splitlines())
    cur = '(toplevel)'
    for idx, ln in enumerate(code, 1):
        m = decl_re.search(ln)
        if m:
            cur = m.group(2)
        for sm in sorry_re.finditer(ln):
            report.append((os.path.relpath(fp, ROOT).replace('\\', '/'), idx, sm.group(1), cur))

for rel, ln, kw, name in report:
    print('%-34s %5d  %-5s %s' % (rel, ln, kw, name))
print('----')
print('带 sorry/admit 的声明总数（按声明去重）: %d' % len(set((r[0], r[3]) for r in report)))
