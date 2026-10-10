import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSource
import Benchmarks.Morpho.MetaMorphoV1_1.MintInternalSource

/-! Optional fee-share minting and the final interest-accrual event. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def accrueFeeRecipient (evm : State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨18⟩) ⟨96⟩).toNat

def accrueInterestCondition : Expr := .binary .ne (.var "feeShares") (.intLit 0)

def accrueInterestMintBody : List Stmt :=
  [.internalCall "_mint" [.storage ⟨"feeRecipient", []⟩, .var "feeShares"] "__c2"]

def accrueInterestFinalBody : List Stmt :=
  [.emit "AccrueInterest" [.var "newTotalAssets", .var "feeShares"], .return [.var cursorName]]

theorem allocatedAccrueInterestFunction_tail :
    allocatedAccrueInterestFunction.body.drop 9 =
      [.ite accrueInterestCondition accrueInterestMintBody []] ++ accrueInterestFinalBody :=
  by decide +kernel

structure AccrueInterestLocals (locals : Store) (total shares cursor : UInt256) : Prop where
  total : locals.get? "newTotalAssets" = some (uint256Value total)
  shares : locals.get? "feeShares" = some (uint256Value shares)
  cursor : locals.get? cursorName = some (uint256Value cursor)
  recipient : locals.get? "feeRecipient" = none

theorem accrueInterestStoredLocals (imms : Store) (ptr lost total shares ptr' : UInt256) :
    AccrueInterestLocals (accrueInterestStoredFrame imms ptr lost total shares ptr').locals
      total shares ptr' := by
  constructor <;> simp [accrueInterestStoredFrame, accrueInterestValuesFrame,
    accrueInterestResumeFrame, cursorResultFrame, allocatedAccruedAssetsFrame,
    cursorName, slotsAndCursorName, Std.HashMap.getElem_insert]

theorem AccrueInterestLocals.afterMint {locals : Store} {total shares cursor : UInt256}
    (hl : AccrueInterestLocals locals total shares cursor) :
    AccrueInterestLocals (locals.insert "__c2" .unit) total shares cursor := by
  constructor
  · rw [store_get_ne _ _ (by decide), hl.total]
  · rw [store_get_ne _ _ (by decide), hl.shares]
  · rw [store_get_ne _ _ (by decide), hl.cursor]
  · rw [store_get_ne _ _ (by decide), hl.recipient]

theorem accrueInterestConditionSource {locals imms : Store} {evm : State}
    {total shares cursor : UInt256} (hl : AccrueInterestLocals locals total shares cursor) :
    evalExpr? config ⟨contract, locals, imms⟩ evm accrueInterestCondition =
      .ok (.bool (decide (shares ≠ ⟨0⟩))) := by
  exact wordNeSource (by simp only [evalExpr?, hl.shares, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]; rfl)

theorem accrueInterestMintArgs {locals imms : Store} {evm : State}
    {total shares cursor : UInt256} (hl : AccrueInterestLocals locals total shares cursor) :
    evalExprs? config ⟨contract, locals, imms⟩ evm
      [.storage ⟨"feeRecipient", []⟩, .var "feeShares"] =
      .ok [.address (accrueFeeRecipient evm), uint256Value shares] := by
  simp only [evalExprs?, evalStorage_feeRecipient evm locals imms hl.recipient, evalExpr?,
    hl.shares, EvalResult.ofOption, bind, EvalResult.bind, pure, accrueFeeRecipient]

theorem accrueInterestFinalSource {locals imms : Store} {evm : State}
    {total shares cursor : UInt256} (hl : AccrueInterestLocals locals total shares cursor) :
    ExecBlock config ⟨contract, locals, imms⟩ evm accrueInterestFinalBody
      (.returned ⟨contract, locals, imms⟩ evm [uint256Value cursor]) := by
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [uint256Value total, uint256Value shares]) ?_)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, hl.cursor, EvalResult.ofOption, bind, EvalResult.bind, pure]
  · simp only [evalExprs?, evalExpr?, hl.total, hl.shares,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem accrueInterestZeroSource {locals imms : Store} {evm : State}
    {total shares cursor : UInt256} (hl : AccrueInterestLocals locals total shares cursor)
    (hzero : shares = ⟨0⟩) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (allocatedAccrueInterestFunction.body.drop 9)
      (.returned ⟨contract, locals, imms⟩ evm [uint256Value cursor]) := by
  rw [allocatedAccrueInterestFunction_tail]
  exact ExecBlock.consNormal (ExecStmt.iteFalse
    (by rw [accrueInterestConditionSource hl]; simp only [hzero, ne_eq, not_true_eq_false,
      decide_false]) ExecBlock.nil) (accrueInterestFinalSource hl)

theorem accrueInterestMintSource {locals imms : Store} {evm : State}
    {total shares cursor : UInt256} (hl : AccrueInterestLocals locals total shares cursor)
    (hne : shares ≠ ⟨0⟩) (hgood : mintAllowed evm (accrueFeeRecipient evm) shares) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (allocatedAccrueInterestFunction.body.drop 9)
      (.returned ⟨contract, locals.insert "__c2" .unit, imms⟩
        (mintBalanceState evm (accrueFeeRecipient evm) shares) [uint256Value cursor]) := by
  rw [allocatedAccrueInterestFunction_tail]
  exact ExecBlock.consNormal (ExecStmt.iteTrue
    (by rw [accrueInterestConditionSource hl, decide_eq_true hne])
    (ExecBlock.consNormal (mintCall (accrueInterestMintArgs hl) hgood) ExecBlock.nil))
    (accrueInterestFinalSource hl.afterMint)

theorem accrueInterestMintReverts {locals imms : Store} {evm : State}
    {total shares cursor : UInt256} (hl : AccrueInterestLocals locals total shares cursor)
    (hne : shares ≠ ⟨0⟩) (hbad : ¬ mintAllowed evm (accrueFeeRecipient evm) shares) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (allocatedAccrueInterestFunction.body.drop 9)
      .reverted := by
  rw [allocatedAccrueInterestFunction_tail]
  exact ExecBlock.consRevert (ExecStmt.iteTrue
    (by rw [accrueInterestConditionSource hl, decide_eq_true hne])
    (ExecBlock.consRevert (mintCallReverts (accrueInterestMintArgs hl) hbad)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
