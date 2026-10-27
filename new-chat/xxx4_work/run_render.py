# -*- coding: utf-8 -*-
"""包装调用 word skill render.py 并打印 manifest（绕开 PowerShell 中文引号参数问题）。"""
import subprocess, sys, os, json

SCRIPT = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.skills\word\scripts\render.py"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXIV-二阶口径数值定向-配对和的离线δ²λ²签名与“二阶也盲”判定.docx"
OUTDIR = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx4_work"

r = subprocess.run([sys.executable, SCRIPT, "render", TARGET, "--output-dir", OUTDIR],
                   capture_output=True, encoding="utf-8", errors="replace", timeout=1800)
print("EXIT:", r.returncode)
print("STDOUT_BEGIN")
print(r.stdout or "")
print("STDOUT_END")
if r.stderr:
    print("STDERR_BEGIN")
    print(r.stderr)
    print("STDERR_END")
# 尝试从输出提取 manifest 路径
m = r.stdout or ""
for line in m.splitlines():
    if "manifest" in line.lower() or "output" in line.lower() or "render-" in line:
        print("HINT:", line)
# 列出 OUTDIR 下最新 render 目录
if os.path.isdir(OUTDIR):
    dirs = [d for d in os.listdir(OUTDIR) if d.startswith("render-")]
    for d in sorted(dirs):
        mp = os.path.join(OUTDIR, d, "render-manifest.json")
        if os.path.isfile(mp):
            print("MANIFEST:", mp)
