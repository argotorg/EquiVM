import Benchmarks.Midnight.LiquidateLoopSourceEntry
import Benchmarks.Midnight.RepayBalanceStorage
import Benchmarks.Midnight.PositionUpdateStorage

variable {fork : Ethereum.Fork}

/-! The first checked position-debt write when liquidation recognizes bad debt. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateBadDebtBody : List Stmt :=
  match liquidateTransition.body[17]! with
  | .ite _ body _ => body
  | _ => []

def liquidateBadDebtState (evm : State) (id borrower badDebt : UInt256) : State :=
  storeLow128 evm (positionSlot id borrower + ⟨2⟩)
    (UInt256.sub (low128 (healthPositionWord evm id borrower)) (low128 badDebt))

theorem assignHealthDebt {frame : Frame} {evm : State} {id borrower : UInt256}
    (value : UInt256) (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType)) :
    assignStorageRef? config frame evm .storage
      { base := "_position", steps := [.field "debt"] } (.int value.toNat) =
      .ok (frame, storeLow128 evm (positionSlot id borrower + ⟨2⟩) value) := by
  apply assignStorageAliasField (name := "_position") (field := "debt")
    (loc := repayDebtLoc id borrower) (t := .int packedUInt128Int)
    (layout := midnightStorageLayout) hp rfl rfl (repayDebt_layout id borrower hcanon)
  simpa only [repayDebtLoc, uint128LowLoc, storeLow128] using
    storageLocStore_uint128_low_word evm (positionSlot id borrower + ⟨2⟩) value

theorem liquidateBadDebtWriteSource {frame : Frame} {evm : State} {id borrower badDebt : UInt256}
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hle : (low128 badDebt).toNat ≤ (low128 (healthPositionWord evm id borrower)).toNat)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config frame evm (liquidateBadDebtBody[0]!)
      (.ok frame (liquidateBadDebtState evm id borrower badDebt)) :=
  ExecStmt.assign (Or.inr hperm)
    (evalCheckedSub128 (evalHealthDebt hcanon hp) (evalCast128 (evalWordLocal hd)) (low128_lt _) hle)
    (assignHealthDebt _ hcanon hp)

theorem liquidateBadDebtWriteStatic {frame : Frame} {evm : State} {id borrower badDebt : UInt256}
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hle : (low128 badDebt).toNat ≤ (low128 (healthPositionWord evm id borrower)).toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt fork config frame evm (liquidateBadDebtBody[0]!) .staticViolation :=
  ExecStmt.assignStatic
    (evalCheckedSub128 (evalHealthDebt hcanon hp) (evalCast128 (evalWordLocal hd)) (low128_lt _) hle)
    (assignHealthDebt _ hcanon hp) hperm

theorem liquidateBadDebtWriteUnderflow {frame : Frame} {evm : State} {id borrower badDebt : UInt256}
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hlt : (low128 (healthPositionWord evm id borrower)).toNat < (low128 badDebt).toNat) :
    ExecStmt fork config frame evm (liquidateBadDebtBody[0]!) .reverted :=
  ExecStmt.assignExprRevert (evalCheckedSubUnderflow ⟨128, by decide⟩ (evalHealthDebt hcanon hp)
    (evalCast128 (evalWordLocal hd)) hlt)

end Benchmarks.Midnight
