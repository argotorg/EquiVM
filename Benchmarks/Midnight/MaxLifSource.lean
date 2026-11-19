import Benchmarks.Midnight.MaxLifTrace
import Benchmarks.Midnight.PositionViewSourceBase

/-! Source execution of `maxLif`, including each checked-arithmetic failure. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def maxLifFunction : FunctionDecl := contract.functions[20]!

def lifComplementExpr (name : Ident) : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.intLit 1000000000000000000) (.var name))

def maxLifFirstArgs : List Expr :=
  [.var "liquidationCursor", lifComplementExpr "lltv", .intLit 1000000000000000000]

def maxLifSecondArgs : List Expr :=
  [.intLit 1000000000000000000, .intLit 1000000000000000000, lifComplementExpr "__c0"]

theorem maxLif_body : maxLifFunction.body =
    [.internalCall "UtilsLib_mulDivDown" maxLifFirstArgs "__c0",
     .internalCall "UtilsLib_mulDivDown" maxLifSecondArgs "__c1", .return [.var "__c1"]] := rfl

theorem evalLifScale {cfg : Config} {frame : Frame} {evm : EVM.State} :
    evalExpr? cfg frame evm (.intLit 1000000000000000000) = .ok (.int lifScale.toNat) := by
  simp only [evalExpr?, pure]; rfl

theorem evalLifComplement {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {w : UInt256} (hget : frame.locals.get? name = some (.int w.toNat))
    (hle : w.toNat ≤ lifScale.toNat) :
    evalExpr? cfg frame evm (lifComplementExpr name) =
      .ok (.int (UInt256.sub lifScale w).toNat) :=
  evalExpr_uint256_sub evalLifScale (evalWordLocal hget) hle

theorem evalLifComplementRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {w : UInt256} (hget : frame.locals.get? name = some (.int w.toNat))
    (hlt : lifScale.toNat < w.toNat) :
    evalExpr? cfg frame evm (lifComplementExpr name) = .revert :=
  evalCheckedSubUnderflow ⟨256, by decide⟩ evalLifScale (evalWordLocal hget) hlt

theorem evalMaxLifFirstArgs {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} (hl : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hc : frame.locals.get? "liquidationCursor" = some (.int cursor.toNat))
    (hle : lltv.toNat ≤ lifScale.toNat) :
    evalExprs? cfg frame evm maxLifFirstArgs =
      .ok [.int cursor.toNat, .int (UInt256.sub lifScale lltv).toNat, .int lifScale.toNat] := by
  simp only [maxLifFirstArgs, evalExprs?, evalWordLocal hc, evalLifComplement hl hle,
    evalLifScale, bind, pure, EvalResult.bind]

theorem evalMaxLifSecondArgs {cfg : Config} {frame : Frame} {evm : EVM.State}
    {w : UInt256} (hw : frame.locals.get? "__c0" = some (.int w.toNat))
    (hle : w.toNat ≤ lifScale.toNat) :
    evalExprs? cfg frame evm maxLifSecondArgs =
      .ok [.int lifScale.toNat, .int lifScale.toNat, .int (UInt256.sub lifScale w).toNat] := by
  simp only [maxLifSecondArgs, evalExprs?, evalLifScale, evalLifComplement hw hle,
    bind, pure, EvalResult.bind]

theorem maxLifSourceReturns {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} (hcontract : frame.contract = contract)
    (hl : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hc : frame.locals.get? "liquidationCursor" = some (.int cursor.toNat))
    (hsafe : MaxLifSafe lltv cursor) :
    ExecFuncBody cfg frame evm maxLifFunction.body
      (.returned (wordLocal (wordLocal frame "__c0" (lifDiscount lltv cursor))
        "__c1" (maxLif lltv cursor)) evm (some [.int (maxLif lltv cursor).toNat])) := by
  rw [maxLif_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (callMulDivDown hcontract (evalMaxLifFirstArgs hl hc hsafe.1)
    hsafe.2.1 (by decide) (name := "__c0"))
  apply ExecBlock.consNormal (callMulDivDown
    (show (wordLocal frame "__c0" (lifDiscount lltv cursor)).contract = contract from hcontract)
    (evalMaxLifSecondArgs (wordLocal_get frame "__c0" _) (Nat.le_of_lt hsafe.2.2))
    (by decide) (lifDenominator_ne_zero hsafe.2.2) (name := "__c1"))
  exact returnInternalResult "__c1" (.int (maxLif lltv cursor).toNat)

theorem maxLifSourceReverts {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} (hcontract : frame.contract = contract)
    (hl : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hc : frame.locals.get? "liquidationCursor" = some (.int cursor.toNat))
    (hbad : ¬ MaxLifSafe lltv cursor) :
    ExecFuncBody cfg frame evm maxLifFunction.body .reverted := by
  rw [maxLif_body]
  apply ExecFuncBody.execBlockRevert
  by_cases hsub : lltv.toNat ≤ lifScale.toNat
  · have hargs := evalMaxLifFirstArgs (cfg := cfg) (evm := evm) hl hc hsub
    by_cases hmul : cursor.toNat * (UInt256.sub lifScale lltv).toNat < UInt256.size
    · apply ExecBlock.consNormal
        (callMulDivDown hcontract hargs hmul (by decide) (name := "__c0"))
      apply ExecBlock.consRevert
      by_cases hsub2 : (lifDiscount lltv cursor).toNat ≤ lifScale.toNat
      · apply callMulDivDownRevert
          (show (wordLocal frame "__c0" (lifDiscount lltv cursor)).contract = contract from hcontract)
          (evalMaxLifSecondArgs (wordLocal_get frame "__c0" _) hsub2)
        intro hs
        have he : lifDiscount lltv cursor = lifScale := u256_inj (by
          have hn : ¬ (lifDiscount lltv cursor).toNat < lifScale.toNat :=
            fun hlt ↦ hbad ⟨hsub, hmul, hlt⟩
          omega)
        apply hs.2
        rw [he, u256_sub_self]
      · apply ExecStmt.internalCallArgsRevert
        change evalExprs? cfg (wordLocal frame "__c0" (lifDiscount lltv cursor)) evm
          maxLifSecondArgs = .revert
        simp only [maxLifSecondArgs, evalExprs?, evalLifScale,
          evalLifComplementRevert (wordLocal_get frame "__c0" _) (Nat.lt_of_not_ge hsub2),
          bind, EvalResult.bind]
    · exact ExecBlock.consRevert (callMulDivDownRevert hcontract hargs (fun hs ↦ hmul hs.1))
  · apply ExecBlock.consRevert
    apply ExecStmt.internalCallArgsRevert
    simp only [maxLifFirstArgs, evalExprs?, evalWordLocal hc,
      evalLifComplementRevert hl (Nat.lt_of_not_ge hsub), bind, EvalResult.bind]

def maxLifArguments (lltv cursor : UInt256) : Store :=
  ((∅ : Store).insert "liquidationCursor" (.int cursor.toNat)).insert "lltv" (.int lltv.toNat)

theorem callMaxLif {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int lltv.toNat, .int cursor.toNat])
    (hsafe : MaxLifSafe lltv cursor) :
    ExecStmt cfg frame evm (.internalCall "maxLif" args name)
      (.ok (wordLocal frame name (maxLif lltv cursor)) evm) := by
  apply internalCallFunctionReturn (callee := maxLifFunction)
    (locals := maxLifArguments lltv cursor) (value := some [.int (maxLif lltv cursor).toNat]) he
  · rw [hc]; rfl
  · rfl
  · apply maxLifSourceReturns (frame := { frame with locals := maxLifArguments lltv cursor })
      hc _ _ hsafe <;>
      simp [maxLifArguments, Std.HashMap.getElem_insert]

theorem callMaxLifRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int lltv.toNat, .int cursor.toNat])
    (hbad : ¬ MaxLifSafe lltv cursor) :
    ExecStmt cfg frame evm (.internalCall "maxLif" args name) .reverted := by
  apply internalCallFunctionRevert (callee := maxLifFunction)
    (locals := maxLifArguments lltv cursor) he
  · rw [hc]; rfl
  · rfl
  · apply maxLifSourceReverts (frame := { frame with locals := maxLifArguments lltv cursor })
      hc _ _ hbad <;>
      simp [maxLifArguments, Std.HashMap.getElem_insert]

end Benchmarks.Midnight
