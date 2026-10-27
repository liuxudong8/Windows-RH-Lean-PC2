# -*- coding: utf-8 -*-
import numpy as np
base = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
for fn in ["zeta_T100000.npz","zeta_T200000.npz","zeta_T400000.npz","zeta_T800000.npz",
           "L_D5_T100000.npz","L_D5_T200000.npz","L_D5_T400000.npz","L_D5_T800000.npz"]:
    d = np.load(base + "\\" + fn)
    for k in d.keys():
        a = d[k]
        print("%s  %s  n=%d  min=%.2f  max=%.2f  sort=%s" % (fn, k, len(a), a.min(), a.max(), bool(np.all(np.diff(a) > 0))))
