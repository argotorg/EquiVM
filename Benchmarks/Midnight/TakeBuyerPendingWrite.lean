import Benchmarks.Midnight.NamedPositionAssign
import Benchmarks.Midnight.TakeSourceFrame
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.WithdrawUnitsWriteBlocksGas
import Benchmarks.Midnight.PackedStorageSourceState
import Benchmarks.Midnight.MemoryFunding

/-! Checked accumulation of the buyer's pending fee after the debt write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyerPendingWriteState (evm : State) (id buyer fee : UInt256) : State :=
  storeHigh128 evm (positionSlot id buyer) (positionFieldWord evm id buyer 1 + fee)

theorem takeBuyerPendingWrite_shape : takeTransition.body.drop 48 =
    takeTransition.body[48]! :: takeTransition.body.drop 49 := rfl

set_option maxRecDepth 10000

theorem midnightTakeBuyerPendingWrite {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata : ByteArray} {aw id buyer fee : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hf : frame.locals.get? "buyerPendingFeeIncrease" = some (.int fee.toNat))
    (hcanon : buyer.toNat < EVM.addressModulus) (hfee : fee.toNat < 2^128)
    (hperm : I.perm = true) (hs : SourceState s0 I σ evm)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨20456⟩
      (positionFieldWord evm id buyer 1 :: fee :: ⟨4216⟩ :: ⟨12386⟩ :: positionSlot id buyer :: R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm (takeTransition.body.drop 48) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ σ' k' C',
      (∀ result, ExecBlock config frame (takeBuyerPendingWriteState evm id buyer fee)
          (takeTransition.body.drop 49) result →
        ExecBlock config frame evm (takeTransition.body.drop 48) result) ∧
      SourceState s0 I σ' (takeBuyerPendingWriteState evm id buyer fee) ∧
      MemoryFunding credit mem aw C' ∧
      RD midnightBytecode I g s0 ⟨12386⟩ (positionSlot id buyer :: R) mem aw rdata σ' k' C' := by
  have he := evalNamedPositionField (evm := evm) 1 hcanon hp
  by_cases hsum : (positionFieldWord evm id buyer 1).toNat + fee.toNat < 2^128
  · obtain ⟨k1, C1, hc1, rd1⟩ := midnightCheckedAdd128_mono
      (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id buyer 1)
      hfee hsum (by jump_dest) rd
    obtain ⟨k2, C2, hc2, rd2⟩ := withdraw_units_block_4216_mono
      (by omega) hperm (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_4216_stack, uint128Mask_computed,
      u256_land_comm (UInt256.lnot uint128Mask), shiftLeft128_highMask,
      u256_land_comm uint128Mask, u256_lor_comm (UInt256.shiftLeft _ _)] at rd2
    let σ' := storeHigh128Accounts σ I (positionSlot id buyer) (positionFieldWord evm id buyer 1 + fee)
    have hs' : SourceState s0 I σ' (takeBuyerPendingWriteState evm id buyer fee) :=
      SourceState.storeHigh128 hs _ _
    refine Or.inr ⟨σ', k2, C2, ?_, hs', ha.mono (by omega), rd2⟩
    intro result hx
    rw [takeBuyerPendingWrite_shape]
    exact ExecBlock.consNormal (ExecStmt.assign (Or.inr (by rw [hs.env]; exact hperm))
      (evalCheckedAdd128 he (evalWordLocal hf) hsum) (assignNamedPositionField 1 _ hcanon hp)) hx
  · refine Or.inl ⟨?_, midnightCheckedAdd128Revert
      (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id buyer 1)
      hfee (Nat.le_of_not_lt hsum) rd⟩
    rw [takeBuyerPendingWrite_shape]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (evalCheckedAdd128Overflow he (evalWordLocal hf) (Nat.le_of_not_lt hsum)))

end Benchmarks.Midnight
