import Examples.Ripemd160Old.JumpGenerated
import Examples.Ripemd160.Fallback
import Lean.Elab.Tactic

/-!
# Old RIPEMD-160 runtime equivalence setup

This proof targets the unoptimized via-IR runtime generated from the original implementation at
evmification commit `51429ca`. The mathematical model and authored Solm behavior are shared with
`Examples.Ripemd160`; only the bytecode reachability layer is specific to this artifact.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Lean Elab Tactic Meta

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

private unsafe def oldDecodeImpl : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := target.eq?
    | throwError "old decode certificate: equality expected"
  let args := lhs.getAppArgs
  unless args.size = 2 do
    throwError "old decode certificate: decode application expected"
  let pc ← unsafe evalExpr UInt256 (mkConst ``UInt256) args[1]!
  let theoremName := Name.str `Ripemd160Old s!"decode_{pc.toNat}"
  let proof := mkConst theoremName
  unless ← isDefEq (← inferType proof) target do
    throwError "old decode certificate {theoremName} does not match the goal"
  goal.assign proof
  replaceMainGoal []

elab "old_decode" : tactic => unsafe oldDecodeImpl

private unsafe def oldJumpImpl : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := target.eq?
    | throwError "old jump certificate: equality expected"
  let args := lhs.getAppArgs
  unless args.size > 0 do
    throwError "old jump certificate: contains application expected"
  let destination ← unsafe evalExpr UInt256 (mkConst ``UInt256) args[args.size - 1]!
  let theoremName := Name.str `Ripemd160Old s!"jump_{destination.toNat}"
  let proof := mkConst theoremName
  unless ← isDefEq (← inferType proof) target do
    throwError "old jump certificate {theoremName} does not match the goal"
  goal.assign proof
  replaceMainGoal []

elab "old_jump" : tactic => unsafe oldJumpImpl

/-- Run a trace using the finite decode and jump certificates for the old 9 KB runtime. -/
syntax "evm_run_rfl " term:max " with " "[" evmStep,* "]" : term

open Lean in
macro_rules
  | `(evm_run_rfl $base:term with [ $steps,* ]) => do
      let mut acc := base
      for s in steps.getElems do
        match s with
        | `(evmStep| raw $op:ident $args*) =>
            acc ← `($(acc).$op $args*)
        | `(evmStep| $op:ident $args*) =>
            match op.getId with
            | `jump    => acc ← `($(acc).jump (by old_decode) $(args[0]!) (by evm_ov))
            | `jumpiT  => acc ← `($(acc).jumpiT (by old_decode) $(args[0]!) $(args[1]!) (by evm_ov))
            | `jumpiNT => acc ← `($(acc).jumpiNT (by old_decode) $(args[0]!) (by evm_ov))
            | _        => acc ← `($(acc).$op $args* (by old_decode) (by evm_ov))
        | _ => Macro.throwUnsupported
      return acc

end Ripemd160Old
