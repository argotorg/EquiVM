import Benchmarks.Midnight.WithdrawBitmapTrace
import Benchmarks.Midnight.WithdrawBitmapSource
import Benchmarks.Midnight.TransferBudget
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-! Joining the optional bitmap clear to the internal health check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem withdrawBitmapPhase {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market newValue index id user assets ret extra : UInt256}
    {token receiver : AccountAddress} {k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hnew : frame.locals.get? "newCollateral" = some (.int newValue.toNat))
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hperm : I.perm = true) (hstack : R.length + 20 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨4624⟩
      ([newValue, index, positionSlot id user, market, id, user, ret, user,
        UInt256.ofNat token.val, UInt256.ofNat receiver.val, assets, id, extra] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ frame' evm' k' C', C ≤ C' ∧
      SourceState s0 I evm'.accountMap evm' ∧
      WithdrawSourceFrame frame' m id user index assets token receiver ∧
      ExecStmt fork config frame evm (withdrawCollateralTransition.body[10]!) (.ok frame' evm') ∧
      RD fork midnightBytecode I g s0 ⟨19775⟩
        ([market, id, user, ret, user, UInt256.ofNat token.val, UInt256.ofNat receiver.val,
          assets, id, extra] ++ R) mem aw rdata evm'.accountMap k' C' := by
  have hg := evalWithdrawClearGuard evm hf hnew
  simp only [List.cons_append, List.nil_append] at rd
  have finishFalse {k1 C1 : Nat} (hc : C ≤ C1)
      (hno : ¬ (newValue = ⟨0⟩ ∧ assets ≠ ⟨0⟩))
      (rd1 : RD fork midnightBytecode I g s0 ⟨4631⟩
        ([⟨0⟩, index, positionSlot id user, market, id, user, ret, user,
          UInt256.ofNat token.val, UInt256.ofNat receiver.val, assets, id, extra] ++ R)
        mem aw rdata evm.accountMap k1 C1) :
      ∃ frame' evm' k' C', C ≤ C' ∧ SourceState s0 I evm'.accountMap evm' ∧
        WithdrawSourceFrame frame' m id user index assets token receiver ∧
        ExecStmt fork config frame evm (withdrawCollateralTransition.body[10]!) (.ok frame' evm') ∧
        RD fork midnightBytecode I g s0 ⟨19775⟩
          ([market, id, user, ret, user, UInt256.ofNat token.val, UInt256.ofNat receiver.val,
            assets, id, extra] ++ R) mem aw rdata evm'.accountMap k' C' := by
    simp only [List.cons_append, List.nil_append] at rd1
    have rd2 := midnightBlocks.midnight_block_4631_fallthrough
      (by simp only [List.length_cons]; omega) rfl rd1
    have rd3 := midnightBlocks.midnight_block_4636
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    exact ⟨frame, evm, k1 + 3 + 5, C1 + 14 + 16, by omega, hs, hf,
      ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hno])) ExecBlock.nil, rd3⟩
  by_cases hz : newValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_4624_taken
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_4802 (R := id :: extra :: R)
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_4802_stack] at rd2
    by_cases ha : assets = ⟨0⟩
    · apply finishFalse (C1 := C + 20 + 23) (by omega)
        (by simp only [ha, ne_self_iff_false, and_false, not_false_eq_true])
      simpa only [ha, show UInt256.isZero (UInt256.isZero ⟨0⟩) = ⟨0⟩ from rfl] using rd2
    · have rd3 := midnightBlocks.midnight_block_4631_taken
        (by simp only [List.length_cons]; omega)
        (by rw [isZero_eq_zero_of_ne ha]; decide) (by jump_dest) rd2
      obtain ⟨k4, C4, hc4, rd4⟩ := withdrawBitmapWrite evm hs.env
        (by simp only [List.length_cons]; omega) hperm rd3
      have rd5 := midnightBlocks.midnight_block_4795 (R := R)
        (by omega) (by jump_dest) rd4
      have rd6 := midnightBlocks.midnight_block_4636
        (by simp only [List.length_cons]; omega) (by jump_dest) rd5
      simp only [midnightBlocks.midnight_block_4636_stack,
        midnightBlocks.midnight_block_4795_stack] at rd6
      let bitmap := bitmapClear (positionBitmapWord evm id user) index
      refine ⟨wordLocal frame "__c2" bitmap, storeHigh128 evm (positionSlot id user + ⟨2⟩) bitmap,
        k4 + 5 + 5, C4 + 18 + 16, by omega, ?_,
        hf.insert "__c2" (.int bitmap.toNat) (by decide), ?_, rd6⟩
      · exact ⟨by simpa only [storeHigh128, storageStore_σ₀] using hs.world,
          by simpa only [storeHigh128_env] using hs.env, rfl⟩
      · exact ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true ⟨hz, ha⟩]))
          (withdrawBitmapSource hf hcanon hi (by rw [hs.env]; exact hperm))
  · have rd1 := midnightBlocks.midnight_block_4624_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hz) rd
    apply finishFalse (C1 := C + 20) (by omega)
      (by simp only [hz, false_and, not_false_eq_true])
    simpa only [midnightBlocks.midnight_block_4624_fallthrough_stack,
      isZero_eq_zero_of_ne hz] using rd1

end Benchmarks.Midnight
