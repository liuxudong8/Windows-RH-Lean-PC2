# -*- coding: utf-8 -*-
"""包装调用 word skill 脚本（绕开 PowerShell 中文引号问题）：audit/render/catalogue/read。"""
import subprocess, sys, os

SKILL = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.skills\word\scripts"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXVI-左尾224审计与威胁形态实证-零点实部实测与盲区威胁收窄判定.docx"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx6_work"

def run(args, timeout=1800):
    r = subprocess.run([sys.executable] + args, capture_output=True, encoding="utf-8",
                       errors="replace", timeout=timeout)
    print("EXIT:", r.returncode)
    if r.stdout:
        print(r.stdout)
    if r.stderr:
        print("STDERR:", r.stderr[:2000])
    return r.returncode

print("===== AUDIT =====")
run([os.path.join(SKILL, "audit.py"), "audit", TARGET])
print("===== RENDER =====")
run([os.path.join(SKILL, "render.py"), "render", TARGET, "--output-dir", OUTDIR])
print("===== CATALOGUE =====")
run([os.path.join(SKILL, "catalogue.py"), "--file", TARGET])
print("===== READ(-d0) =====")
run([os.path.join(SKILL, "read.py"), TARGET, "-d", "0", "-o",
     os.path.join(OUTDIR, "read0.txt")])
