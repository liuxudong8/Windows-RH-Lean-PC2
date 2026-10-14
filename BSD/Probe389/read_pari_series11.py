# -*- coding: utf-8 -*-
"""389a1/p=11 series(11) 复刻: PARI 真模符号管道.
验证: T^2 || L_11(T) mod 11^k (ord_T = 2).
校准: 11a1/p=3 同结构 Σ=68 命中 (read_pari_recompute.py).
389a1: N=389, rank 2, a_11 = -4, Δ=389>0 ⟹ real_components=2; M(0)=0 (实测) ⟹ 无常数校正.
"""
import re
import sys
sys.path.insert(0, r"C:\proj2\BSD\Probe389")
from fractions import Fraction as F
from l11_series import series_lp, fmt_series, f2padic, modinv, alpha_ordinary, teichmuller, e_bounds

# ---------- 1. parse PARI 输出 ----------
pari121, pari11 = {}, {}
m0 = None
raw = []
with open(r"C:\proj2\BSD\Probe389\ms389a1_series_out.txt", encoding="utf-8") as fh:
    for line in fh:
        line = line.strip()
        if not line or line == "DONE":
            continue
        m = re.match(r"M\(0\)=([^\s]+)", line)
        if m:
            m0 = F(m.group(1))
            continue
        m = re.match(r"j=(\d+) a=(\d+) r(\d+)=(\d+)/(\d+):\s*([^\s]+)", line)
        if m:
            j, a = int(m.group(1)), int(m.group(2))
            r = F(int(m.group(4)), int(m.group(5)))
            val = F(m.group(6))
            raw.append((j, a, r, val))
            (pari121 if m.group(3) == "121" else pari11)[r] = val

# ---------- 2. 一致性检查 (重复点值一致) ----------
seen, dups_ok = {}, True
for (j, a, r, val) in raw:
    if r in seen:
        if seen[r] != val:
            print("INCONSISTENT:", r, seen[r], "vs", val)
            dups_ok = False
    else:
        seen[r] = val
print("M(0) =", m0, "| distinct r121:", len(pari121), "| distinct r11:", len(pari11), "| dups consistent:", dups_ok)
assert m0 == 0 and dups_ok

def lam(r):
    d = pari121 if r.denominator == 121 else pari11
    return d[r]

# ---------- 2b. parse 补测 (ms389a1_dist_out.txt: {0,1}, 分母 1331; ms389a1_dist2_out.txt: 分母 121 分布点) ----------
pari_other = {}
for _f in (r"C:\proj2\BSD\Probe389\ms389a1_dist_out.txt", r"C:\proj2\BSD\Probe389\ms389a1_dist2_out.txt"):
    with open(_f, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            m = re.match(r"\{0,(\d+)/(\d+)\}\s*=\s*([^\s]+)", line)
            if m:
                r = F(int(m.group(1)), int(m.group(2)))
                pari_other[r] = F(m.group(3))
            m2 = re.match(r"\{0,1\}\s*=\s*([^\s]+)", line)
            if m2:
                pari_other[F(1)] = F(m2.group(1))
print("pari_other keys:", len(pari_other))

# ---------- 3. 分布恒等式自洽检查 (389a1, p=11, a_11=-4) ----------
def try_lam(r):
    for d in (pari121, pari11, pari_other):
        if r in d:
            return d[r]
    return None

print("\n--- 分布恒等式检查 (389a1, p=11, a_11=-4) ---")
ap = -4
for rr, tag in [(F(1, 121), "r=1/121"), (F(1, 11), "r=1/11")]:
    lhs = ap * try_lam(rr)
    terms = [try_lam((rr + F(m)) / 11) for m in range(11)]
    extra = try_lam(11 * rr)
    if lhs is None or any(t is None for t in terms) or extra is None:
        print("%s: SKIP (仍有缺测点)" % tag)
    else:
        rhs = sum(terms) + extra
        print("%s: a_p·f = %s | Σ_m f((r+m)/11) = %s | + f(pr) = %s | 总和 = %s | 成立: %s"
              % (tag, lhs, sum(terms), extra, rhs, lhs == rhs))

# ---------- 4. series(11) 复刻 ----------
out = series_lp(p=11, ap=-4, lam=lam, real_components=2, n=2, prec=5, eta=0, c_bound=0)
print("\n--- L_11(T) series(11) ---")
print(fmt_series(out, 11))
for l, (c, bd) in enumerate(out):
    print("T^%d: c = %d mod 11^%d | mod 11 = %d | 估值 v_11 ≥ %d" % (l, c, bd, c % 11, bd))
t0, t1, t2 = out[0][0], out[1][0], out[2][0]
print("\nord_T 判定: T0 ≡ 0 mod 11^%d: %s | T1 ≡ 0 mod 11: %s | T2 ≢ 0 mod 11: %s" % (
    out[0][1], t0 % 11 == 0, t1 % 11 == 0, t2 % 11 != 0))
print("结论: ord_T =", 2 if (t0 % 11 == 0 and t1 % 11 == 0 and t2 % 11 != 0) else "?")
