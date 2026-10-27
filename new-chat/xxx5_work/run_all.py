# -*- coding: utf-8 -*-
"""包装调用 word skill audit.py/render.py 并完整打印（绕开 PowerShell 中文参数问题）。"""
import subprocess, sys, os

SKILL = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.skills\word\scripts"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXV-盲区理论门槛文献核实-零密度路径闭合与超密度假设判定.docx"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx5_work"

def run(args, timeout=1800):
    r = subprocess.run([sys.executable] + args, capture_output=True, encoding="utf-8",
                       errors="replace", timeout=timeout)
    print("EXIT:", r.returncode)
    if r.stdout:
        print(r.stdout)
    if r.stderr:
        print("STDERR:", r.stderr[:3000])
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
