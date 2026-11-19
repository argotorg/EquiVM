import Benchmarks.Midnight.PositionUpdateDecreaseSource

/-! Source execution of the four position-field assignments, including static rejection. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem positionUpdateAssignmentsSource {frame : Frame} {evm : EVM.State}
    {id user credit pending : UInt256} {result : ExecResult}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hcredit : frame.locals.get? "newCredit" = some (.int credit.toNat))
    (hpending : frame.locals.get? "newPendingFee" = some (.int pending.toNat))
    (hcanon : user.toNat < EVM.addressModulus) (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config frame (positionUpdateState evm id user credit pending)
      (positionUpdateFunction.body.drop 11) result) :
    ExecBlock config frame evm (positionUpdateFunction.body.drop 7) result := by
  let s1 := storeLow128 evm (positionSlot id user) credit
  let s2 := storeLow128 s1 (positionSlot id user + ⟨1⟩) (marketLossWord s1 id)
  let s3 := storeHigh128 s2 (positionSlot id user) pending
  have hp1 : s1.executionEnv.perm = true := by simpa only [s1, storeLow128_env] using hperm
  have hp2 : s2.executionEnv.perm = true := by simpa only [s2, storeLow128_env] using hp1
  have hp3 : s3.executionEnv.perm = true := by simpa only [s3, storeHigh128_env] using hp2
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (evalWordLocal hcredit)
    (assignPositionAliasField 0 credit hcanon hp)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hp1)
    (evalMarketLoss (evm := s1) hc hbase hid) (assignPositionAliasField 2 (marketLossWord s1 id) hcanon hp)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hp2) (evalWordLocal hpending)
    (assignPositionAliasField 1 pending hcanon hp)) ?_
  have ht : evalExpr? config frame s3 (.cast (.env .timestamp) (.elem (.int packedUInt128Int))) =
      .ok (.int (low128 (UInt256.ofNat evm.executionEnv.header.timestamp)).toNat) := by
    apply evalCast128
    simp only [evalExpr?, envValue, s3, s2, s1, storeHigh128_env, storeLow128_env,
      pure, Int.ofNat_eq_natCast]
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hp3) ht ?_) htail
  have hs := assignPositionAliasField (evm := s3) 3
    (low128 (UInt256.ofNat evm.executionEnv.header.timestamp)) hcanon hp
  simpa only [positionFieldStore, positionFieldSlot, show (3 : Fin 4).val % 2 ≠ 0 by decide,
    show ¬ (3 : Fin 4).val < 2 by decide, if_false, storeHigh128_low] using hs

theorem positionUpdateAssignmentsStatic {frame : Frame} {evm : EVM.State} {id user credit : UInt256}
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hcredit : frame.locals.get? "newCredit" = some (.int credit.toNat))
    (hcanon : user.toNat < EVM.addressModulus) (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm (positionUpdateFunction.body.drop 7) .staticViolation := by
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (evalWordLocal hcredit) (assignPositionAliasField 0 credit hcanon hp) hperm

theorem positionUpdateWrites_get (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    let frame := positionUpdateWritesFrame evm imms m id user
    frame.contract = contract ∧ frame.locals.get? "marketState" = none ∧
    frame.locals.get? "id" = some (wordBytes32Value id) ∧
    frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType) ∧
    frame.locals.get? "newCredit" = some (.int (positionNewCredit evm m id user).toNat) ∧
    frame.locals.get? "newPendingFee" = some (.int (positionNewPending evm m id user).toNat) ∧
    frame.locals.get? "accruedFee" = some (.int (positionViewFee evm m id user).toNat) ∧
    frame.locals.get? "creditDecrease" = some (.int (positionCreditDecrease evm m id user).toNat) ∧
    frame.locals.get? "pendingFeeDecrease" = some (.int (positionPendingDecrease evm m id user).toNat) ∧
    frame.locals.get? "user" = some (.address (AccountAddress.ofNat user.toNat)) := by
  simp [positionUpdateWritesFrame, positionUpdateCreditFrame, positionUpdateValuesFrame,
    wordLocal, positionUpdateTupleFrame, resumeAfterInternalCall, positionViewAliasFrame,
    positionViewCallFrame, positionViewArguments, Std.HashMap.getElem_insert]

theorem positionUpdateSourceStatic (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user)
    (hc : (positionNewCredit evm m id user).toNat ≤ (positionFieldWord evm id user 0).toNat)
    (hp : (positionNewPending evm m id user).toNat ≤ (positionFieldWord evm id user 1).toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply (positionUpdateWritesPrefix evm imms m id user hcanon hsafe hc hp).run
  have hg := positionUpdateWrites_get evm imms m id user
  exact positionUpdateAssignmentsStatic hg.2.2.2.1 hg.2.2.2.2.1 hcanon hperm

end Benchmarks.Midnight
