import Benchmarks.EAS.EAS.Common

variable {fork : Ethereum.Fork}
open Stele
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: an ordered sequence of pure Boolean guards.
theorem execRequires {cfg : Config} {frame : Frame} {evm : EVM.State}
    (checks : List (Expr × Bool))
    (he : ∀ p ∈ checks, evalExpr? cfg frame evm p.1 = .ok (.bool p.2)) :
    if checks.all (·.2) then
      ExecBlock fork cfg frame evm (checks.map fun p => Stmt.require p.1) (.ok frame evm)
    else ExecBlock fork cfg frame evm (checks.map fun p => Stmt.require p.1) .reverted := by
  induction checks with
  | nil => exact ExecBlock.nil
  | cons p rest ih =>
    have hfirst := he p List.mem_cons_self
    have hrest := ih (fun q hq => he q (List.mem_cons_of_mem p hq))
    rcases p with ⟨expr,b⟩
    cases b with
    | false =>
      simp only [List.all_cons,Bool.false_and,Bool.false_eq_true,if_false,List.map_cons]
      exact ExecBlock.consRevert (ExecStmt.requireFalse hfirst)
    | true =>
      cases hb : rest.all (·.2) <;>
        simp only [List.all_cons,Bool.true_and,hb,Bool.false_eq_true,if_false,if_true,List.map_cons] at hrest ⊢
      all_goals exact ExecBlock.consNormal (ExecStmt.requireTrue hfirst) hrest

end Benchmarks.EAS.EAS
