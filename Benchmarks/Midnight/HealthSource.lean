import Benchmarks.Midnight.HealthSourceFrame

variable {fork : Ethereum.Fork}

/-! The storage-reading prefix, debt guard, and Boolean return of the health function. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def healthArguments (m : MarketData) (id user : UInt256) : Store :=
  (((∅ : Store).insert "borrower" (.address (AccountAddress.ofNat user.toNat))).insert
    "id" (wordBytes32Value id)).insert "market" (Model.marketValue m.value)

def healthCallFrame (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  { contract := contract, locals := healthArguments m id user, immutables := imms }

def healthAliasFrame (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  { (healthCallFrame imms m id user) with
    locals := (healthArguments m id user).insert "_position"
      (.storageRef (positionRef id user) positionType) }

def healthDebtFrame (imms : Store) (m : MarketData) (id user word : UInt256) : Frame :=
  wordLocal (wordLocal (healthAliasFrame imms m id user) "_debt" (low128 word)) "maxDebt" ⟨0⟩

def healthLoopFrame (imms : Store) (m : MarketData) (id user word : UInt256) : Frame :=
  wordLocal (healthDebtFrame imms m id user word) "_collateralBitmap"
    (UInt256.shiftRight word (UInt256.ofNat 128))

theorem healthSourcePrefix (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) (hcanon : user.toNat < EVM.addressModulus) :
    ABlock fork config evm (healthCallFrame imms m id user) healthFunction.body
      (healthDebtFrame imms m id user (healthPositionWord evm id user))
      (healthFunction.body.drop 3) := by
  have ha : ABlock fork config evm (healthCallFrame imms m id user) healthFunction.body
      (healthAliasFrame imms m id user) (healthFunction.body.drop 1) := by
    refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
    apply resolvePositionBorrower rfl
    · simp [healthCallFrame, healthArguments]
    · simp [healthCallFrame, healthArguments, Std.HashMap.getElem_insert]
    · simp [healthCallFrame, healthArguments, Std.HashMap.getElem_insert]
  have ha1 := ha.letStep (evalHealthDebt (evm := evm) hcanon (store_get_self _ _ _))
  exact ha1.letStep (by simp only [evalExpr?, pure]; rfl)

theorem healthDebtFrame_alias (imms : Store) (m : MarketData) (id user word : UInt256) :
    (healthDebtFrame imms m id user word).locals.get? "_position" =
      some (.storageRef (positionRef id user) positionType) := by
  simp only [healthDebtFrame,
    wordLocal_get_ne _ _ _ _ (show "maxDebt" ≠ "_position" from by decide),
    wordLocal_get_ne _ _ _ _ (show "_debt" ≠ "_position" from by decide),
    healthAliasFrame, store_get_self]

theorem healthDebtFrame_debt (imms : Store) (m : MarketData) (id user word : UInt256) :
    (healthDebtFrame imms m id user word).locals.get? "_debt" = some (.int (low128 word).toNat) := by
  simp only [healthDebtFrame, wordLocal_get_ne _ _ _ _ (show "maxDebt" ≠ "_debt" from by decide),
    wordLocal_get]

theorem healthLoopFrame_inv (imms : Store) (m : MarketData) (id user word : UInt256) :
    HealthSourceFrame (healthLoopFrame imms m id user word) m id user
      (UInt256.shiftRight word (UInt256.ofNat 128)) ⟨0⟩ (low128 word) := by
  constructor <;> simp [healthLoopFrame, healthDebtFrame, healthAliasFrame, healthCallFrame,
    healthArguments, wordLocal, Std.HashMap.getElem_insert]

theorem evalHealthDebtGuard {cfg : Config} {frame : Frame} {evm : EVM.State} {debt : UInt256}
    (hd : frame.locals.get? "_debt" = some (.int debt.toNat)) :
    evalExpr? cfg frame evm (.binary .gt (.var "_debt") (.intLit 0)) =
      .ok (.bool (decide (0 < debt.toNat))) := by
  simp only [evalExpr?, hd, EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?]
  simp only [Int.natCast_pos]

theorem healthSourceReturn {cfg : Config} {frame : Frame} {evm : EVM.State} {debt maxDebt : UInt256}
    (hd : frame.locals.get? "_debt" = some (.int debt.toNat))
    (hm : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat)) :
    ExecBlock fork cfg frame evm (healthFunction.body.drop 4)
      (.returned frame evm (some [.bool (decide (debt.toNat ≤ maxDebt.toNat))])) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, hd, hm, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  simp only [Int.ofNat_le]

theorem healthBoolWord (debt maxDebt : UInt256) :
    UInt256.isZero (UInt256.lt maxDebt debt) =
      if decide (debt.toNat ≤ maxDebt.toNat) then ⟨1⟩ else ⟨0⟩ := by
  by_cases hle : debt.toNat ≤ maxDebt.toNat
  · rw [ult_zero hle, decide_eq_true hle]; rfl
  · rw [ult_one (by omega), decide_eq_false hle]; rfl

end Benchmarks.Midnight
