# -*- coding: utf-8 -*-
"""统计 c:\proj2\OrderPreservingBijection 下 Lean 源码中的 sorry/axiom/admit。
规则：
- 只统计非注释代码（剔除 -- 行注释与 /- -/ 块注释）
- sorry: 词法 \bsorry\b（不含 sorryAx）
- admit: \badmit\b（Lean 中 admit 等价 sorry）
- axiom: 词法 \baxiom\b 出现次数；并单独提取顶层 axiom 声明名
"""
import os, re, sys

ROOT = r'C:\proj2\OrderPreservingBijection'

def strip_comments(lines):
    """返回去掉注释后的代码行列表（保留行号映射）。"""
    out = []
    in_block = False
    for ln in lines:
        # 去掉块注释
        res = ''
        i = 0
        s = ln
        while i < len(s):
            if in_block:
                j = s.find('-/', i)
                if j == -1:
                    i = len(s)
                else:
                    in_block = False
                    i = j + 2
            else:
                j = s.find('/-', i)
                k = s.find('--', i)
                if j == -1 and k == -1:
                    res += s[i:]
                    i = len(s)
                elif j != -1 and (k == -1 or j < k):
                    res += s[i:j]
                    in_block = True
                    i = j + 2
                else:
                    res += s[i:k]
                    i = len(s)
        out.append(res)
    return out

def main():
    files = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        for fn in filenames:
            if fn.endswith('.lean') and '.bak' not in fn:
                files.append(os.path.join(dirpath, fn))
    files.sort()

    total = {'sorry': 0, 'axiom': 0, 'admit': 0}
    main_sorry = 0   # 主库（非 test_ 前缀）
    test_sorry = 0
    main_axiom = 0
    test_axiom = 0
    axiom_names = []
    rows = []

    for fp in files:
        with open(fp, encoding='utf-8', errors='replace') as f:
            code = strip_comments(f.read().splitlines())
        cnt = {'sorry': 0, 'axiom': 0, 'admit': 0}
        for ln in code:
            cnt['sorry'] += len(re.findall(r'\bsorry\b', ln))
            cnt['admit'] += len(re.findall(r'\badmit\b', ln))
            cnt['axiom'] += len(re.findall(r'\baxiom\b', ln))
            for m in re.finditer(r'^\s*axiom\s+([A-Za-z_][A-Za-z0-9_\.]*)', ln):
                axiom_names.append((os.path.relpath(fp, ROOT), m.group(1)))
        rel = os.path.relpath(fp, ROOT).replace('\\', '/')
        is_test = os.path.basename(rel).startswith('test_') or rel.startswith('test_')
        rows.append((rel, cnt['sorry'], cnt['axiom'], cnt['admit'], is_test))
        for k in cnt:
            total[k] += cnt[k]
        if is_test:
            test_sorry += cnt['sorry']; test_axiom += cnt['axiom']
        else:
            main_sorry += cnt['sorry']; main_axiom += cnt['axiom']

    print('%-52s %5s %5s %5s' % ('FILE', 'sorry', 'axiom', 'admit'))
    print('-' * 70)
    for rel, s, a, d, _ in rows:
        if s or a or d:
            print('%-52s %5d %5d %5d' % (rel, s, a, d))
    print('-' * 70)
    print('TOTAL  files=%d  sorry=%d  axiom=%d  admit=%d' % (len(files), total['sorry'], total['axiom'], total['admit']))
    print('主库(非test): sorry=%d  axiom=%d' % (main_sorry, main_axiom))
    print('test文件:     sorry=%d  axiom=%d' % (test_sorry, test_axiom))
    print('axiom 声明:')
    for rel, name in axiom_names:
        print('   %s : %s' % (rel, name))

if __name__ == '__main__':
    main()
