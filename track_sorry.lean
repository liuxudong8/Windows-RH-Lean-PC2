import OrderPreservingBijection

open Lean Elab Command

namespace Trace

/-- 收集表达式中引用的所有常量名（结构递归，安全终止） -/
def addConsts (e : Expr) (s : NameSet) : NameSet :=
  match e with
  | .const n _ => s.insert n
  | .app f a => addConsts a (addConsts f s)
  | .lam _ _ b _ => addConsts b s
  | .forallE _ _ b _ => addConsts b s
  | .letE _ _ v b _ => addConsts b (addConsts v s)
  | .mdata _ e' => addConsts e' s
  | .proj _ _ e' => addConsts e' s
  | _ => s

/-- 取声明体（v4.34 的 ConstantInfo.value? 对 thmInfo 无效，直接 match 构造器） -/
def declValue (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- 是否属于本项目库（按声明所属模块判断）；admit 是 Init 例外，需展开 -/
def isOurs (env : Environment) (n : Name) : Bool :=
  n == `admit ||
    match env.getModuleFor? n with
    | some m => m.toString.startsWith "OrderPreservingBijection"
    | none => false

/-- DFS：返回 root 依赖闭包中所有「定义项直接含 sorryAx」的声明及其路径。
     只递归库内声明与 admit；mathlib/Init 其余声明不含 sorryAx，跳过。
     深度上限 10000，visited 防环。 -/
def findLeaves (env : Environment) (root : Name) : List (Name × List Name) :=
  let rec go : Name → List Name → NameSet → Nat → List (Name × List Name) → List (Name × List Name) :=
    fun n path vis depth acc =>
      if depth = 0 then acc
      else if vis.contains n then acc
      else
        match env.find? n with
        | none => acc
        | some ci =>
          let vis' := vis.insert n
          let p' := n :: path
          match declValue ci with
          | none => acc
          | some val =>
            let cs := addConsts val ∅
            if cs.contains `sorryAx then
              (n, p') :: acc
            else if not (isOurs env n) then
              acc
            else
              cs.toList.foldl (fun a c => go c p' vis' (depth - 1) a) acc
  termination_by n path vis depth acc => depth
  go root [] ∅ 10000 []

def traceAll (env : Environment) (roots : List Name) : List String :=
  roots.flatMap fun root =>
    let leaves := findLeaves env root
    let head := s!"=== {root} ==="
    let body :=
      if leaves.isEmpty then ["  (依赖闭包中不含 sorryAx)"]
      else leaves.map fun (n, p) =>
        s!"  {n}   via  {String.intercalate " <- " (p.reverse.map (·.toString))}"
    head :: body

end Trace

open Trace

run_cmd do
  let env ← getEnv
  let roots : List Name :=
    [ `RHSpectralDuality.riemann_hypothesis
    , `RHSpectralDuality.all_zeros_on_critical_line
    , `RHSpectralDuality.weil_explicit_formula_trivial_terms_cancel
    , `RHSpectralDuality.nontrivial_zero_sum_pair_separation
    , `RHSpectralDuality.off_critical_line_contradiction
    , `RHSpectralDuality.mollified_trace_equality
    , `RHSpectralDuality.weil_explicit_formula ]
  for line in traceAll env roots do
    logInfo line
