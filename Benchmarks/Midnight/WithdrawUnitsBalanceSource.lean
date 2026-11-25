import Benchmarks.Midnight.WithdrawUnitsSourceFrame
import Benchmarks.Midnight.ToUint128Source

variable {fork : Ethereum.Fork}

/-! Checked uint128 subtraction from a storage field after converting withdrawal units. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawUnitsSubtractStmts (name : Ident) (ref : StorageRef) : List Stmt :=
  [.internalCall "UtilsLib_toUint128" [.var "units"] name,
    .assign .storage ref (.inRange packedUInt128Int
      (.binary .sub (.storage ref) (.var name)))]

theorem withdrawUnitsSubtractSource {frame : Frame} {evm evm' : EVM.State}
    {old units : UInt256} {name : Ident} {ref : StorageRef}
    (hc : frame.contract = contract)
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hread : evalExpr? config (wordLocal frame name units) evm (.storage ref) =
      .ok (.int old.toNat))
    (hstore : assignStorageRef? config (wordLocal frame name units) evm .storage ref
      (.int (UInt256.sub old units).toNat) = .ok (wordLocal frame name units, evm'))
    (hold : old.toNat < 2^128) (h128 : units.toNat < 2^128) (hle : units.toNat ≤ old.toNat)
    (hperm : evm.executionEnv.perm = true) {tail : List Stmt} {result : ExecResult}
    (htail : ExecBlock fork config (wordLocal frame name units) evm' tail result) :
    ExecBlock fork config frame evm (withdrawUnitsSubtractStmts name ref ++ tail) result := by
  have he : evalExprs? config frame evm [.var "units"] = .ok [.int units.toNat] := by
    simp only [evalExprs?, evalWordLocal hu, EvalResult.bind, bind, pure]
  apply ExecBlock.consNormal (callToUint128 hc he h128 (name := name))
  exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalCheckedSub128 hread (evalWordLocal (wordLocal_get ..)) hold hle) hstore) htail

theorem withdrawUnitsSubtractUnderflow {frame : Frame} {evm : EVM.State}
    {old units : UInt256} {name : Ident} {ref : StorageRef}
    (hc : frame.contract = contract)
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hread : evalExpr? config (wordLocal frame name units) evm (.storage ref) =
      .ok (.int old.toNat))
    (h128 : units.toNat < 2^128) (hlt : old.toNat < units.toNat) (tail : List Stmt) :
    ExecBlock fork config frame evm (withdrawUnitsSubtractStmts name ref ++ tail) .reverted := by
  have he : evalExprs? config frame evm [.var "units"] = .ok [.int units.toNat] := by
    simp only [evalExprs?, evalWordLocal hu, EvalResult.bind, bind, pure]
  apply ExecBlock.consNormal (callToUint128 hc he h128 (name := name))
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalCheckedSubUnderflow ⟨128, by decide⟩ hread (evalWordLocal (wordLocal_get ..)) hlt))

end Benchmarks.Midnight
