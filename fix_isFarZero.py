# -*- coding: utf-8 -*-
import io
path = r"c:\proj2\OrderPreservingBijection\stage_4.lean"
with io.open(path, "r", encoding="utf-8", newline="") as f:
    text = f.read()
n1 = text.count("ρ ∈ farZeroSubtype")
text = text.replace("ρ ∈ farZeroSubtype", "IsFarZero ρ")
n2 = text.count("提取拖走")
text = text.replace("提取拖走", "挖掉")
with io.open(path, "w", encoding="utf-8", newline="") as f:
    f.write(text)
print("replaced 'ρ ∈ farZeroSubtype':", n1, "| '提取拖走':", n2)
