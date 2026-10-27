# -*- coding: utf-8 -*-
"""包装调用 word skill audit.py 并完整打印（绕开 PowerShell 中文引号参数问题）。"""
import subprocess, sys, json, re

SCRIPT = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.skills\word\scripts\audit.py"
TARGET = r"D:\F\有名公司同事文档\刘旭东文集\document\d1\路2攻防XXXVI-左尾224审计与威胁形态实证-零点实部实测与盲区威胁收窄判定.docx"

r = subprocess.run([sys.executable, SCRIPT, "audit", TARGET],
                   capture_output=True, encoding="utf-8", errors="replace", timeout=600)
print("EXIT:", r.returncode)
out = r.stdout or ""
print("STDOUT_BEGIN")
print(out)
print("STDOUT_END")
if r.stderr:
    print("STDERR_BEGIN")
    print(r.stderr)
    print("STDERR_END")
m = re.search(r"BEGIN AUDIT REPORT JSON(.*?)END AUDIT REPORT JSON", out, re.S)
if m:
    try:
        rep = json.loads(m.group(1))
        print("error_count:", rep.get("error_count"))
        print("error_summary:", json.dumps(rep.get("error_summary"), ensure_ascii=False))
        print("automated_status:", rep.get("automated_status"))
        wc = rep.get("word_count") or rep.get("stats") or {}
        print("word_count:", wc)
    except Exception as e:
        print("JSON parse fail:", e)
