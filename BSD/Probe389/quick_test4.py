# quick_test4.py — independent check of a_n assembly via modular Fricke duality:
#   f(i/(N*t)) = epsN * N * (i*t)^2 * f(i*t)  (weight 2)  =>  f(i/N) = -epsN*N*f(i)
import sys, math
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P

an389 = P.gen_a_n(6000, 0, 1, 1, -2, 0, bad_ap={389: 1})
an37 = P.gen_a_n(6000, 0, 0, 1, -1, 0, bad_ap={37: 1})

for name, an, N in (('389a1', an389, 389), ('37a1', an37, 37)):
    fi = sum(an[n] * math.exp(-2 * math.pi * n) for n in range(1, 20))   # fast decay
    # f(i/N): slow decay e^{-2pi n/N}; sum until terms ~1e-14
    fiN = 0.0
    for n in range(1, 6001):
        t = math.exp(-2 * math.pi * n / N)
        fiN += an[n] * t
        if t < 1e-15:
            break
    ratio = fiN / (N * fi) if fi != 0 else float('nan')
    print(f'{name}: f(i)={fi:.8f}  f(i/{N})={fiN:.8f}  fiN/(N*fi)={ratio:.4f}  (expect +1 or -1)')
