f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 修复1: 删除"连续谱项的数学地位"注释，合并到磨光迹等式注释中
old_comment = """/-- 连续谱项的数学地位（说明）：
    连续谱 Cont(f) = (1/2πi)∫ (φ'/φ)(1/2+ir) f(1/4+r²) dr 一般不为零。
    由留数定理+散射矩阵函数方程，Cont(f) = trivialZeroContribution(f)
    （见 continuousTerm_eq_trivialZeroContribution 公理，在 trivialZeroContribution 定义之后）。
    因此在磨光迹等式中，连续谱项与平凡零点贡献抵消，最终得到 spectralSum = nontrivialZeroSum。
    这比旧框架假设 continuousTerm=0 更数学正确。 -/

/-- 磨光迹等式（定理，由 Arthur 迹公式 + 磨光性质推出）：
    对磨光测试函数 f，迹公式简化为：
      spectralSum f = geometricSum f
    证明：
    (1) Arthur 迹公式：spectralSum + continuousTerm = geometricSum + ellipticTerm
    (2) ellipticTerm f = 0（f.ellipticVanishes）
    (3) continuousTerm f = 0（mollified_continuous_spectrum_vanishes）
    代入即得。
    这是 MEF 推导的起点：谱侧与几何侧的纯等式。 -/
theorem mollified_trace_equality (f : MollifiedTestFunction) :
    spectralSum f.toTestFunction = geometricSum f.toTestFunction := by
  have h_atf : spectralSum f.toTestFunction + continuousTerm f.toTestFunction =
      geometricSum f.toTestFunction + ellipticTerm f.toTestFunction :=
    arthur_trace_formula f.toTestFunction
  have h_ellip : ellipticTerm f.toTestFunction = 0 := f.ellipticVanishes
  have h_cont : continuousTerm f.toTestFunction = 0 :=
    mollified_continuous_spectrum_vanishes f
  rw [h_ellip, h_cont] at h_atf
  simpa using h_atf"""

new_comment = """/-- 磨光迹等式（定理，由 Arthur 迹公式 + 连续谱=平凡贡献 + 椭圆项消失推出）：
    对磨光测试函数 f，迹公式简化为：
      spectralSum f + trivialZeroContribution f = geometricSum f
    证明：
    (1) Arthur 迹公式：spectralSum + continuousTerm = geometricSum + ellipticTerm
    (2) ellipticTerm f = 0（f.ellipticVanishes）
    (3) continuousTerm f = trivialZeroContribution f（continuousTerm_eq_trivialZeroContribution）
    代入即得。
    后续与 Weil 显式公式 geometricSum = nontrivialZeroSum + trivialZeroContribution 联立，
    消去 trivialZeroContribution，得到 spectralSum = nontrivialZeroSum。 -/
theorem mollified_trace_equality (f : MollifiedTestFunction) :
    spectralSum f.toTestFunction + trivialZeroContribution f.toTestFunction =
    geometricSum f.toTestFunction := by
  have h_atf : spectralSum f.toTestFunction + continuousTerm f.toTestFunction =
      geometricSum f.toTestFunction + ellipticTerm f.toTestFunction :=
    arthur_trace_formula f.toTestFunction
  have h_cont : continuousTerm f.toTestFunction = trivialZeroContribution f.toTestFunction :=
    continuousTerm_eq_trivialZeroContribution f.toTestFunction
  have h_ellip : ellipticTerm f.toTestFunction = 0 := f.ellipticVanishes
  rw [h_cont, h_ellip] at h_atf
  simpa using h_atf"""

content = content.replace(old_comment, new_comment, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: fixed mollified_trace_equality')
