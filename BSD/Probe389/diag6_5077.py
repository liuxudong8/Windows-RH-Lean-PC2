# diag6_5077.py : mpmath high-precision check of F'(1) and L'''/6
# If mpmath (80 dps) gives F'(1) ~ 0 and L'''/6 ~ 1.73185, the defect is in float gamma_upper's s-derivative.
# If mpmath reproduces -0.148, the defect is in the formula/assembly.
import mpmath as mp
mp.mp.dps = 80

N = 5077
EPS = -1
Q = 2000  # small Q fine here: we are comparing two implementations, same truncation
SQN = mp.sqrt(N)

from probe5077_numeric import gen_a_n
an = gen_a_n(4000)

def F_mp(s):
    gs = mp.gamma(s)
    g2s = mp.gamma(2 - s)
    S1 = mp.mpf('0'); S2 = mp.mpf('0')
    for n in range(1, Q + 1):
        bn = 2 * mp.pi * n / SQN
        # gamma(s,bn)/Gamma(s) = P(s,bn) regularized lower incomplete gamma
        p1 = mp.gammainc(s, 0, bn) / gs
        p2 = mp.gammainc(2 - s, 0, bn) / g2s
        nm = mp.mpf(n)
        S1 += an[n] * nm ** (-s) * p1
        S2 += an[n] * nm ** (s - 2) * p2
    C = N ** (1 - s) * (2 * mp.pi) ** (2 * s - 2) / gs
    return S1 + C * S2 / EPS

h = mp.mpf('0.01')
F1 = F_mp(mp.mpf(1))
slope = (F_mp(1 + h) - F_mp(1 - h)) / (2 * h)
cubic = (F_mp(1 + 2*h) - 2*F_mp(1 + h) + 2*F_mp(1 - h) - F_mp(1 - 2*h)) / (2 * h**3)
print("mpmath dps=80, Q=2000:")
print("F(1)         =", mp.nstr(F1, 20))
print("slope F'(1)  =", mp.nstr(slope, 20), "  (rank 3: must be 0)")
print("L'''/6       =", mp.nstr(cubic / 6, 20), "  (Cremona 1.73184990)")
