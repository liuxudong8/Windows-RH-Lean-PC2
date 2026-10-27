# -*- coding: utf-8 -*-
"""攻防 XXXVII 四合一：生成 + audit + render + catalogue + read（run_all.py，d1 惯例）"""
import subprocess, sys, os, json, glob

PY_DEFAULT = sys.executable          # 默认 python（python-docx）
SKILL = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.skills\word"
WORK = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx7_work"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXVII-Weil显式公式实部口径注入敏感性-离线对同虚部成对的间距结构排除与N_off·δ²·λ²累积可测性判定.docx"
GEN = os.path.join(WORK, "gen_docx_xxxvii.py")

def run(argv, cwd=None):
    r = subprocess.run(argv, shell=False, cwd=cwd, capture_output=True, encoding="utf-8", errors="strict", timeout=900)
    print("CMD:", " ".join(argv[:3]), "... exit=", r.returncode)
    out = (r.stdout or "") + (r.stderr or "")
    if out.strip():
        print(out[-3000:])
    return r

# 1 生成
run([PY_DEFAULT, GEN])

# 2 audit
run([PY_DEFAULT, os.path.join(SKILL, "scripts", "audit.py"), "audit", TARGET])

# 3 render
man = run([PY_DEFAULT, os.path.join(SKILL, "scripts", "render.py"), "render", TARGET,
           "--output-dir", WORK])
# 解析 manifest 路径
m = glob.glob(os.path.join(WORK, "render-*", "render-manifest.json"))
print("MANIFESTS:", m)
if m:
    mm = sorted(m)[-1]
    with open(mm, encoding="utf-8") as fp:
        d = json.load(fp)
    print("RENDER pages:", d.get("page_count"), "sha256:", d.get("input", {}).get("sha256", "?")[:16])

# 4 catalogue
run([PY_DEFAULT, os.path.join(SKILL, "scripts", "catalogue.py"), "--file", TARGET])

# 5 read 正文
run([PY_DEFAULT, os.path.join(SKILL, "scripts", "read.py"), TARGET, "-d", "0", "-o",
     os.path.join(WORK, "read0.txt")])
print("ALL DONE")
