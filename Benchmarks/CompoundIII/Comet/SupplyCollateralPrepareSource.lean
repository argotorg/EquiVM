import Benchmarks.CompoundIII.Comet.SupplyCollateralAfterSource
import Benchmarks.CompoundIII.Comet.SafeUintSource
import Benchmarks.CompoundIII.Comet.IndexAccrual

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def supplyCollateralTransferredFrame (imms : Store) (sender dst asset : AccountAddress)
    (requested received : UInt256) : Frame :=
  let frame := supplyCollateralEntry imms sender dst asset requested
  { frame with locals := frame.locals.insert "__c0" (.int received.toNat) }

def supplyCollateralPreparedFrame (imms : Store) (sender dst asset : AccountAddress)
    (requested received : UInt256) : Frame :=
  let frame := supplyCollateralTransferredFrame imms sender dst asset requested received
  { frame with
    locals := (frame.locals.insert "__c1" (.int received.toNat)).insert "amount" (.int received.toNat) }

def supplyCollateralPrepare : List Stmt :=
  [.internalCall "safe128" [.var "__c0"] "__c1",
    .assign .localVar ⟨"amount", []⟩ (.var "__c1")]

theorem supplyCollateralPrepare_source (imms : Store) (sender dst asset : AccountAddress)
    (requested received : UInt256) (evm : EVM.State) :
    ExecBlock config (supplyCollateralTransferredFrame imms sender dst asset requested received)
      evm supplyCollateralPrepare
      (if received.toNat < 2^128 then
        .ok (supplyCollateralPreparedFrame imms sender dst asset requested received) evm
        else .reverted) := by
  let frame := supplyCollateralTransferredFrame imms sender dst asset requested received
  have hc := safeUint_call ⟨128, by decide⟩ "safe128" safe128Callable_lookup frame evm received
    (.var "__c0") "__c1" rfl (by
      simp only [evalExpr?, frame, supplyCollateralTransferredFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
  change ExecStmt _ _ _ _ (if received.toNat < 2^128 then _ else _) at hc
  by_cases hw : received.toNat < 2^128
  · rw [if_pos hw] at hc ⊢
    apply ExecBlock.consNormal hc
    have he : evalExpr? config
        { frame with locals := frame.locals.insert "__c1" (.int received.toNat) }
        evm (.var "__c1") = .ok (.int received.toNat) := by
      simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    apply ExecBlock.consNormal (ExecStmt.assign he ?_) .nil
    apply assignLocalFrame (old := .int requested.toNat)
    simp only [frame, supplyCollateralTransferredFrame, supplyCollateralEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
  · rw [if_neg hw] at hc ⊢
    exact ExecBlock.consRevert hc

theorem supplyCollateralPrepared_args (imms : Store) (sender dst asset : AccountAddress)
    (requested received : UInt256) (out : ByteArray) :
    let frame := supplyCollateralPreparedFrame imms sender dst asset requested received
    SupplyCollateralArgs { frame with locals := frame.locals.insert "assetInfo" (assetValue out) }
      sender dst asset received out := by
  dsimp only
  constructor <;> simp only [supplyCollateralPreparedFrame, supplyCollateralTransferredFrame,
    supplyCollateralEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty] <;> rfl

end Benchmarks.CompoundIII.Comet
