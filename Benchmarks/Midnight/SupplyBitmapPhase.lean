import Benchmarks.Midnight.SupplyBitmapSource
import Benchmarks.Midnight.SupplyBitmapTrace
import Benchmarks.Midnight.TransferBudget

/-! Paired source and bytecode execution of the bitmap phase. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyBitmapPhase {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw ignored root id user index : UInt256}
    {credit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 15 ≤ 1024)
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat)) (hindex : index.toNat < 128)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨17274⟩
      (ignored :: positionSlot id user :: index :: R) mem aw rdata evm.accountMap k C) :
    (RDrev midnightBytecode g s0 ∧
      ExecBlock config frame evm (supplyNewCollateralBody.drop 2) .reverted) ∨
    (RDstatic midnightBytecode g s0 ∧
      ExecBlock config frame evm (supplyNewCollateralBody.drop 2) .staticViolation) ∨
    (I.perm = true ∧ ∃ k' C',
      let bitmap := bitmapSet (positionBitmapWord evm id user) index
      let evm' := storeHigh128 evm (positionSlot id user + ⟨2⟩) bitmap
      TransferBudget root credit mem aw C' ∧
      ExecBlock config frame evm (supplyNewCollateralBody.drop 2)
        (.ok (supplyCountFrame frame bitmap) evm') ∧
      RD midnightBytecode I g s0 ⟨17462⟩ (index :: R) mem aw rdata evm'.accountMap k' C') := by
  rcases supplyBitmapWrite evm henv hstack hindex rd with ⟨hperm, hr⟩ |
    ⟨hperm, k1, C1, hmono, rd1⟩
  · exact Or.inr (Or.inl ⟨hr, supplyBitmapStatic hc hcanon hp hi hindex
      (by rw [henv]; exact hperm)⟩)
  · let bitmap := bitmapSet (positionBitmapWord evm id user) index
    rcases midnightBitmapCountGuard (R := index :: R)
        (by simp only [List.length_cons]; omega) rd1 with ⟨hcount, hr⟩ |
          ⟨hcount, k2, C2, hmono2, rd2⟩
    · refine Or.inl ⟨hr, supplyBitmapSource hc hcanon hp hi hindex
        (by rw [henv]; exact hperm) ?_⟩
      change 16 < (bitmapCount bitmap).toNat at hcount
      apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      simpa only [decide_eq_false (show ¬ (bitmapCount bitmap).toNat ≤ 16 by omega)] using
        evalSupplyCountGuard frame
          (storeHigh128 evm (positionSlot id user + ⟨2⟩) bitmap) bitmap
    · refine Or.inr (Or.inr ⟨hperm, k2, C2, (hb.mono hmono).mono hmono2,
        supplyBitmapSource hc hcanon hp hi hindex (by rw [henv]; exact hperm) ?_, rd2⟩)
      change (bitmapCount bitmap).toNat ≤ 16 at hcount
      apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) (ExecBlock.nil ..)
      simpa only [decide_eq_true hcount] using evalSupplyCountGuard frame
        (storeHigh128 evm (positionSlot id user + ⟨2⟩) bitmap) bitmap

end Benchmarks.Midnight
