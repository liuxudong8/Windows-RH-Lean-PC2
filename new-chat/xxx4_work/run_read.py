# -*- coding: utf-8 -*-
"""包装调用 word skill read.py（-d 0）并打印（绕开 PowerShell 中文引号参数问题）。"""
import subprocess, sys

SCRIPT = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.skills\word\scripts\read.py"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXIV-二阶口径数值定向-配对和的离线δ²λ²签名与“二阶也盲”判定.docx"
OUTFILE = r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\xxx4_work\read0.txt"

r = subprocess.run([sys.executable, SCRIPT, TARGET, "-d", "0", "-o", OUTFILE],
                   capture_output=True, encoding="utf-8", errors="replace", timeout=600)
print("EXIT:", r.returncode)
if r.stdout:
    print(r.stdout[:2000])
if r.stderr:
    print("STDERR:", r.stderr[:2000])
