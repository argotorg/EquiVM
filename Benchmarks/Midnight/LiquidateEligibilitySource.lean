import Benchmarks.Midnight.LiquidateEligibility

/-! Source execution of the liquidation lock lookup and eligibility requirement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateLockFrame (frame : Frame) (evm : State) (id borrower : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c11" (lockValue evm liquidationLockBase id borrower) }

set_option maxRecDepth 2000000 in
theorem liquidateEligibilitySource {frame : Frame} {evm : State} {m : MarketData}
    {id target seized repaid borrower mode bitmap maxDebt price originalDebt badDebt : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id target seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus) (rest : List Stmt) :
    let lock := Stele.EVM.transientLoad evm evm.executionEnv.codeOwner
      (lockSlot liquidationLockBase id borrower)
    (¬ LiquidateEligible evm.executionEnv m lock mode originalDebt maxDebt ∧
      ExecBlock config frame evm ((liquidateTransition.body.drop 15).take 2 ++ rest) .reverted) ∨
    (LiquidateEligible evm.executionEnv m lock mode originalDebt maxDebt ∧
      ABlock config evm frame ((liquidateTransition.body.drop 15).take 2 ++ rest)
        (liquidateLockFrame frame evm id borrower) rest) := by
  dsimp only
  let f1 := liquidateLockFrame frame evm id borrower
  let lock := Stele.EVM.transientLoad evm evm.executionEnv.codeOwner
    (lockSlot liquidationLockBase id borrower)
  have hargs : evalExprs? config frame evm [.var "id", .var "borrower"] =
      .ok [wordBytes32Value id, .address (AccountAddress.ofNat borrower.toNat)] := by
    simp only [evalExprs?, evalExpr?, hf.idValue, hf.borrowerValue,
      EvalResult.ofOption, pure, bind, EvalResult.bind]
  have hcall : ExecStmt config frame evm (liquidateTransition.body[15]!) (.ok f1 evm) :=
    callLiquidationLocked hf.contract hargs hcanon
  have hf1 : LiquidateSourceFrame f1 m id target seized repaid borrower mode receiver callback data :=
    hf.insert _ _ (by decide)
  have ha1 : LiquidateAccumulators f1 bitmap maxDebt price originalDebt badDebt :=
    ha.insert _ _ (by decide)
  have hl : f1.locals.get? "__c11" = some (wordToElem .bool lock) :=
    store_get_self frame.locals "__c11" (lockValue evm liquidationLockBase id borrower)
  have he := evalLiquidateEligibility (evm := evm) hl hf1.mode hf1.market ha1.originalDebt ha1.maxDebt
  by_cases hel : LiquidateEligible evm.executionEnv m lock mode originalDebt maxDebt
  · exact Or.inr ⟨hel, ⟨fun h ↦ ExecBlock.consNormal hcall (ExecBlock.consNormal
      (ExecStmt.requireTrue (he.trans (by rw [decide_eq_true hel]))) h)⟩⟩
  · exact Or.inl ⟨hel, ExecBlock.consNormal hcall (ExecBlock.consRevert
      (ExecStmt.requireFalse (he.trans (by rw [decide_eq_false hel]))))⟩

end Benchmarks.Midnight
