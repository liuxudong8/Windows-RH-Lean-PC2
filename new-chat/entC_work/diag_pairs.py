# -*- coding: utf-8 -*-
import numpy as np
NPZ = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter\zeros_T6e5.npz"
d = np.load(NPZ)
g = np.sort(np.asarray(d["zeta"], dtype=np.float64))
LAM = np.log(6e5); W = 2.5/LAM
print("n=", len(g), "W=", W, "spacing mean=", float(np.diff(g).mean()), "min=", float(np.diff(g).min()))
seg = g[:5000]
cnt = np.array([int(np.searchsorted(seg, seg[i]+W, side="right")-i-1) for i in range(5000)])
print("hand counts total=", int(cnt.sum()), "mean=", float(cnt.mean()))
ends = np.searchsorted(g, g+W, side="right")
counts = ends - np.arange(len(g)) - 1
print("vec counts total=", int(counts.sum()), "mean=", float(counts.mean()))
e2 = np.searchsorted(g[:5000], g[:5000]+W, side="right")
c2 = e2 - np.arange(5000) - 1
print("vec(5000) total=", int(c2.sum()), "match hand:", bool(np.array_equal(cnt, c2)))
dg = np.diff(g)
print("frac spacing<W(0.188):", float((dg<W).mean()), " frac<0.5:", float((dg<0.5).mean()), " frac<1:", float((dg<1.0).mean()))
