import Mathlib.Tactic

namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: expose lower bounds for subtraction without splitting every underflow case.
theorem natSubLowerBound (a b : Nat) : a ≤ a-b+b := by omega

open Lean Meta Elab Tactic in
elab "nat_sub_bounds" : tactic => withMainContext do
  let target ← getMainTarget
  let mut goal ← getMainGoal
  let (_, proofs) ← (target.forEach (m := StateRefT (Array Lean.Expr) TacticM) fun e => do
    let args := e.getAppArgs
    if e.isAppOfArity ``HSub.hSub 6 && args[0]!.isConstOf ``Nat then
      let proof ← mkAppM ``natSubLowerBound #[args[4]!, args[5]!]
      modify (·.push proof)).run #[]
  for proof in proofs do
    let (_, next) ← goal.note (← mkFreshUserName `hsub) proof
    goal := next
  replaceMainGoal [goal]

end Benchmarks.UniswapV4PoolManager
