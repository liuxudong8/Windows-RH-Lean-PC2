# -*- coding: utf-8 -*-
"""攻防 XXXVIII 四合一：生成 + audit + render + catalogue + read（run_all.py，d1 惯例）"""
import subprocess, sys, os, json, glob

PY_DEFAULT = sys.executable
SKILL = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.skills\word"
WORK = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx8_work"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXVIII-Δ常数指纹对同虚部成对注入的爆炸响应与威胁排除的交叉验证闭合.docx"
GEN = os.path.join(WORK, "gen_docx_xxxviii.py")

def run(argv, cwd=None):
    r = subprocess.run(argv, shell=False, cwd=cwd, capture_output=True, encoding="utf-8", errors="strict", timeout=900)
    print("CMD:", " ".join(argv[:3]), "... exit=", r.returncode)
    out = (r.stdout or "") + (r.stderr or "")
    if out.strip():
        print(out[-3000:])
    return r

run([PY_DEFAULT, GEN])
run([PY_DEFAULT, os.path.join(SKILL, "scripts", "audit.py"), "audit", TARGET])
man = run([PY_DEFAULT, os.path.join(SKILL, "scripts", "render.py"), "render", TARGET, "--output-dir", WORK])
m = glob.glob(os.path.join(WORK, "render-*", "render-manifest.json"))
print("MANIFESTS:", m)
if m:
    mm = sorted(m)[-1]
    with open(mm, encoding="utf-8") as fp:
        d = json.load(fp)
    print("RENDER pages:", d.get("page_count"), "sha256:", d.get("input", {}).get("sha256", "?")[:16])
run([PY_DEFAULT, os.path.join(SKILL, "scripts", "catalogue.py"), "--file", TARGET])
run([PY_DEFAULT, os.path.join(SKILL, "scripts", "read.py"), TARGET, "-d", "0", "-o",
     os.path.join(WORK, "read0.txt")])
print("ALL DONE")
