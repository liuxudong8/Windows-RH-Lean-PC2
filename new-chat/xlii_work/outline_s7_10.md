# 攻防 XLII S7.10 落档大纲：prime_weight_bounds 降定理（Khat 特化）

## 文档定位
- 体裁：通用文档（研究攻坚记录，d1 惯例，非正式论文）
- 输出：中文 d1 根 + 英文 d1\en
- 命名（中文）：路2攻防XLII-S7.10-prime_weight_bounds降定理-Khat特化与素数项界真证.docx
- 命名（英文）：路2攻防XLII-S7.10-prime_weight_bounds-theorem-Khat-specialization-EN.docx
- 篇幅：约 4–5 页，无目录（短文）
- 公式：OMML（Word 原生公式），禁 LaTeX 源码；正文可读纯文本 + 上下标

## 章节与事实依据
1. **任务与结论**
   - 任务：把素数项权重件 prime_weight_bounds（原 axiom）降为真证 theorem；prime_sum_bound 特化到 K := Khat
   - 结论：全量 lake build QRH 2704 jobs exit=0，无 warning
2. **数学口径：b_n = n^{−1/2}·K̂(δ·log n) 的有界/平滑件**
   - 关键判定：Khat_abs_le 是分式上界，分母 |√2±2πu| 在 u=±√2/(2π) 为零 → 非全局一致界，给不出常数
   - 正确工具：|sin t| ≤ |t|（Real.abs_sin_le_abs）→ 每项 |sin(t)/(2t)| ≤ 1/2 → 全局一致界
     B = 1/(√2·|sin(1/√2)|)
   - 有界分支：|b_n| ≤ (√n)⁻¹·B
   - 平滑分支分解：Δb_n = A·(K̂_{n+1}−K̂_n) + (A−C)·K̂_n
     （A=(√(n+1))⁻¹、C=(√n)⁻¹）
   - 四件：|log(n+1)−log n| ≤ 1/n；A ≤ C；C·C = n⁻¹；|A−C| ≤ C³（有理化 √(n+1)−√n = 1/(√(n+1)+√n)，分母 ≥ √n³）
   - 组装常数 M = L·δ + B（L 为 K̂ 的 Lipschitz 常数）
3. **Lean 实现**
   - Core §4b：abs_sin_div_two_mul_le_half（t=0 除零惯例 subst t; simp）、khat_global_bound（真证）；命名 axiom fourierCos_Khat（连接件）、khat_lipschitz（光滑件，∃L）
   - Main：log_succ_sub_le_inv、inv_sqrt_succ_le、inv_sqrt_sq_eq_inv、inv_sqrt_succ_sub_le（真证链）→ prime_weight_bounds_Khat → prime_sum_bound 特化（去 K/hKs，bgs5_khat_fourier_supp 前移到 primeSum 后）
   - 踩坑记录：脚本幂等替换误伤（fourierCos Khat → Khathat，2 处）；le_add_of_nonneg_left/right 方向；field_simp 处理逆；双 doc 注释致语法错误
4. **编译证据**
   - Core 14s ✔、Main 11s ✔、Stage3 22s ✔、QRH 9.6s ✔，2704 jobs exit=0
   - 顺带清理 6 处历史 unused 变量 warning（_ 前缀）
5. **残余 axiom 与下一步**
   - 残余：fourierCos_Khat（连接件）、khat_lipschitz（光滑件）、bgs5_khat_fourier_supp（积分层窄支撑）
   - 下一步：khat_lipschitz 的 L 由解析式可算（带限整函数），可用导数件真证（S7.1 Stage 3+ 清单）

## 引用核查
- 无外部文献引用；全部内容来自本轮 Lean 工程实际状态（C:\proj2\QRH 四源文件、dbg_build.txt 编译输出）
