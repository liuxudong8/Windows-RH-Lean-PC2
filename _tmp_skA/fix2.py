# -*- coding: utf-8 -*-
import io
p = r'C:\Users\shtcl\Doubao\chats\2026-10-02\new-chat\_tmp_skA\gen_skA.py'
s = io.open(p, encoding='utf-8').read()
old = '显式公式中"素数项与轨道项"的接口'
new = '显式公式中“素数项与轨道项”的接口'
assert old in s, 'pattern missing'
s = s.replace(old, new)
io.open(p, 'w', encoding='utf-8').write(s)
print('OK')
