f = r'C:\proj2\OrderPreservingBijection\stage_4.lean'
with open(f, 'r', encoding='utf-8') as fh:
    content = fh.read()

# 1. 从当前位置删除 mollified_trace_equality（注释+定理）
old_block = """/-- 磨光迹等式（定理，由 Arthur 迹公式 + 连续谱=平凡贡献 + 椭圆项消失推出）：
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
  simpa using h_atf

"""

content = content.replace(old_block, "", 1)

# 2. 在 continuousTerm_eq_trivialZeroContribution 公理之后插入
insert_after = """axiom continuousTerm_eq_trivialZeroContribution (f : TestFunction) :
    continuousTerm f = trivialZeroContribution f

"""

insert_block = """axiom continuousTerm_eq_trivialZeroContribution (f : TestFunction) :
    continuousTerm f = trivialZeroContribution f

/-- 磨光迹等式（定理，由 Arthur 迹公式 + 连续谱=平凡贡献 + 椭圆项消失推出）：
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
  simpa using h_atf

"""

content = content.replace(insert_after, insert_block, 1)

with open(f, 'w', encoding='utf-8') as fh:
    fh.write(content)
print('Done: moved mollified_trace_equality after continuousTerm_eq_trivialZeroContribution')
