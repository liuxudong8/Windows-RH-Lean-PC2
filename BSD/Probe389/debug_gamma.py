import sys
sys.path.insert(0, r'C:\proj2\BSD\Probe389')
import probe389_numeric as P
import math

s = 2.5
gs = math.gamma(s)
print('Gamma(2.5) =', gs)
for x in (0.319, 1.0, 5.0, 10.0, 15.0, 19.9, 20.0, 30.0, 60.0, 200.0):
    g = P.gamma_upper(s, x)
    print(f'x={x:8.3f}  Gamma(s,x)={g:.10f}  ratio={g/gs:.6f}  (must be <= 1)')
