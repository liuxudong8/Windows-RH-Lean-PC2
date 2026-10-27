# -*- coding: utf-8 -*-
"""S2(ii) 新四档零点生成：T=1e5/2e5/4e5/8e5，每档 ζ 与 L(χ₅) 并行。
用既有 gen_zeta_generic.py（ζ）与 gen_L_generic.py（L，D=5）。
输出到 tmp_word_scatter：zeta_T<n>.npz / L_D5_T<n>.npz。
日志：s2ii_gen.log（每作业追加）。
"""
import subprocess, time, os, sys

BASE = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
GEN_Z = os.path.join(BASE, "gen_zeta_generic.py")
GEN_L = os.path.join(BASE, "gen_L_generic.py")
PY = r"D:\F\Anaconda3\anaconda_3\python.exe"
LOG = os.path.join(BASE, "s2ii_gen.log")

def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    with open(LOG, "a", encoding="utf-8") as f:
        f.write(s + "\n")

TS = [1.0e5, 2.0e5, 4.0e5, 8.0e5]
t_start = time.time()
for T in TS:
    jobs = [
        ("zeta", [GEN_Z, str(int(T)), "zeta_T%d.npz" % int(T)]),
        ("L5", [GEN_L, "5", str(int(T)), "L_D5_T%d.npz" % int(T), "0.02"]),
    ]
    procs = {}
    for tag, argv in jobs:
        log("START %s T=%d  %s" % (tag, int(T), " ".join(argv)))
        p = subprocess.Popen([PY] + argv, cwd=BASE, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
        procs[tag] = p
    for tag, p in procs.items():
        out, _ = p.communicate()
        dt = time.time() - t_start
        tail = (out or "").strip().splitlines()
        last = tail[-2:] if tail else ["(no output)"]
        log("[%.0fs] %s T=%d rc=%d :: %s" % (dt, tag, int(T), p.returncode, " | ".join(last)))
        if p.returncode != 0:
            log("[ERR] %s" % out[:2000])
log("ALL DONE  total %.0fs" % (time.time() - t_start))
