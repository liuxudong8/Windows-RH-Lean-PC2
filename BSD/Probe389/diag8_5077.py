# diag8_5077.py : mpmath UPPER-incomplete (same structure as float pipeline) slope for 5077
# float pipeline: S1 uses Gamma(s,bn)/Gamma(s)  (upper incomplete) -> slope -0.147728 (Q-independent).
# If mpmath upper-incomplete gives slope ~ 0  (rank 3), float gamma_upper has an s-derivative bug.
# If mpmath upper-incomplete also gives -0.1477, the formula structure itself carries it (both curves would show it).
import math
import mpmath as mpm
mpm.mp.dps = 60

from probe5077_numeric import N, EPS, gen_a_n

Q = 4000
an = gen_a_n(20000)
SQN = mpm.sqrt(N)

def F_up(s, Q):
    gs = mpm.gamma(s); g2s = mpm.gamma(2 - s)
    S1 = mpm.mpf('0'); S2 = mpm.mpf('0')
    for n in range(1, Q + 1):
        bn = 2 * mpm.pi * n / SQN
        up1 = (gs - mpm.gammainc(s, 0, bn)) / gs      # Gamma(s,bn)/Gamma(s) = 1 - P
        up2 = (g2s - mpm.gammainc(2 - s, 0, bn)) / g2s
        nm = mpm.mpf(n)
        S1 += an[n] * nm ** (-s) * up1
        S2 += an[n] * nm ** (s - 2) * up2
    C = N ** (1 - s) * (2 * mpm.pi) ** (2 * s - 2) / gs
    return S1 + C * S2 / EPS

print("mpmath UPPER-incomplete (structure == float pipeline), 5077a1:")
for Q in (1000, 2000, 4000, 8000):
    h = mpm.mpf('0.01')
    sl = (F_up(1 + h, Q) - F_up(1 - h, Q)) / (2 * h)
    print(f"Q={Q:5d}  slope F'(1) = {mpm.nstr(sl, 12)}   (float gives -0.147728231; rank 3: 0)")
