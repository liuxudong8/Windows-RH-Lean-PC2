# outline.md — S7.12 落档

## 文档定位
- 类型：技术攻坚记录（数学研究笔记，内部文档）
- 主写作类型：通用文档（general.md）
- 语种：中文（d1）＋ 英文（d1\en）
- 篇幅：约 2000–2500 字（中文），无字数硬约束
- 目录：不生成（用户未要求，且篇幅不达强制阈值）
- 编号体系：阿拉伯小数层级（1 / 1.1 / 1.1.1）
- 公式：Word 原生 Unicode 可读数学文本（K̂、∫、π、·、⁻¹、|a|、≤），禁 LaTeX 源码

## 事实依据（全部来自本会话 Lean 攻坚实录，无外部引用，无需联网）
- Core.lean：`axiom fourierCos` → `noncomputable def fourierCos (K z) := ∫ x, K x * Real.cos (2*Real.pi*z*x)`
- Stage3.lean：`axiom fourierCos_scale` → `lemma fourierCos_scale`（真证体，四段 calc）
- 探针三版：dbg_fourier_probe1/2/3.txt（Import 缺失、命名空间陷阱、积分件清单）
- 构建：dbg_build_fourier.txt，2704 jobs、exit=0、0 error、0 warning
- 使用点：n1_diag_invariant（z=0）、n1_offdiag_scale_eq（z=2δ）签名不变

## 文档结构
1. 结论摘要
2. 背景与定位（fourierCos 在 S7.1 形式化 / N1 超支撑件中的角色；axiom 积压）
3. 口径变更一：fourierCos 本体真定义（Bochner 积分；不可积惯例 0；兼容性；保留 axiom）
4. 口径变更二：fourierCos_scale 缩放律真证（陈述；四段证明链；关键件；使用点无损）
5. 旧结论修正：IntervalIntegral 依赖判断的推翻（旧判断；实证否决；死路清单勿重试）
6. 构建验证（2704 绿；探针清理）
7. 残余命名 axiom 状态表（按文件归属）

## 关键数值/事实（必须与实录一致）
- C_MT = 1/2 + (1/√2)·cot(1/√2) ≈ 1.3274992963（不涉及，仅背景）
- 证明链可用件：integral_const_mul / integral_congr_ae / Measure.integral_comp_inv_mul_left（全空间、无正则性前提）
- 不存在件：全空间 integral_congr、integral_comp_mul_left、volume_map_mul_left、map_mul_left、Integral.olean

## 验收
- audit 0 errors；render 逐页视觉检查；catalogue（无 TOC 域不动作）
- 文件名：
  - 中文：路2攻防XLII-S7.12-fourierCos真定义与fourierCos_scale缩放律真证.docx
  - 英文：路2攻防XLII-S7.12-fourierCos-definition-and-scale-lemma-EN.docx
