# -*- coding: utf-8 -*-
"""生成 389a1/p=11 series(11) 的 PARI 求值脚本 (220 点: j=0..10, a=1..10; r121+r11)."""
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from l11_series import teichmuller, e_bounds

p, ap, n, prec = 11, -4, 2, 5
bounds = [None] + [b for b in e_bounds(n - 1, prec, p)[1:]]
padic_prec = max(bounds[1:]) + 5
gamma = 1 + p
teich = [teichmuller(a, p, padic_prec) for a in range(p)]

lines = []
lines.append("default(parisize, 256M);")
lines.append('f = "/tmp/ms389a1_series_out.txt";')
lines.append("E = ellinit([0,1,1,-2,0]);")
lines.append("MS = msfromell(E, 1);")
lines.append("M = MS[1];")
lines.append("v = MS[2];")
lines.append('write(f, Str("M(0)=", mseval(M, v, [1,0;0,1])));')
cnt = 0
for j in range(p ** (n - 1)):
    gamma_power = pow(gamma, j)
    for a in range(1, p):
        b = teich[a] * gamma_power
        c121 = b % (p * p)
        c11 = b % p
        lines.append('write(f, Str("j=%d a=%d r121=%d/121:", mseval(M, v, [0,1;%d,121])));' % (j, a, c121, c121))
        lines.append('write(f, Str("j=%d a=%d r11=%d/11:", mseval(M, v, [0,1;%d,11])));' % (j, a, c11, c11))
        cnt += 2
lines.append('write(f, "DONE");')
lines.append("quit();")
with open(r"C:\proj2\BSD\Probe389\ms389a1_series.gp", "w", encoding="utf-8") as fh:
    fh.write("\n".join(lines))
print("points written:", cnt, "; script lines:", len(lines))
print("padic_prec =", padic_prec, "teich[1..3] =", teich[1], teich[2], teich[3])
