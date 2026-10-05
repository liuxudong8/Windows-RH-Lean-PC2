import re

# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 把 Finset.sup Finset.univ (fun x : {x : ℝ // True} => ...) 改成 Supr 或者 iSup
# 实际上，我们需要的是 sup_x ‖h''(x)‖，也就是上确界

# 先把所有的 Finset.sup Finset.univ (fun x : {x : ℝ // True} => ...) 替换成 (iSup (fun x : ℝ => ...))
content = re.sub(
    r'Finset\.sup Finset\.univ \(fun x : \{x : ℝ // True\} =>\s*‖\(deriv \(deriv ([^)]+)\) x\.val‖\)',
    r'iSup (fun x : ℝ => ‖(deriv (deriv \1) x)‖)',
    content
)

# 写回文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8', newline='') as f:
    f.write(content)

print('Done!')
