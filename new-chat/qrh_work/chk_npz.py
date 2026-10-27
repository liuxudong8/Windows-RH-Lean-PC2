# -*- coding: utf-8 -*-
import numpy as np
base = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
for fn in ["zeros_v2.npz", "zeros_small.npz", "L_D5_T1e4.npz", "L_D5_TT1e4.npz", "L_D5_TT4e4.npz", "L_D5_T2e4_corr.npz"]:
    d = np.load(base + "\\" + fn)
    keys = list(d.keys())
    info = ", ".join("%s=%d" % (k, len(d[k])) for k in keys)
    print(fn, "->", info)
