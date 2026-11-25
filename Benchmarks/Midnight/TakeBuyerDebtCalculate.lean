import Benchmarks.Midnight.TakeBuyerDebtSource
import Benchmarks.Midnight.CheckedSubGas
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.RuntimeBlocks_027
import Benchmarks.Midnight.RuntimeBlocks_047

variable {fork : Ethereum.Fork}

/-! Computing the buyer's bounded debt subtraction before the first trade write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

set_option maxHeartbeats 400000 in
theorem midnightTakeBuyerDebtCalculate {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw units buyerSlot debt buyerDebt sellerSlot marketSlot
      decrease ratifierPtr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024) (hd : buyerDebt.toNat < 2^128)
    (hunits : calldataWord I.calldata 68 = units)
    (rd : RD fork midnightBytecode I g s0 ⟨12316⟩
      ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr,
        zeroFloorSubWord units buyerDebt] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨12353⟩
      ([UInt256.sub buyerDebt (takeBuyerRepayment units buyerDebt), uint128Mask, buyerSlot,
        debt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, sellerSlot, marketSlot, decrease,
        ratifierPtr, zeroFloorSubWord units buyerDebt] ++ R) mem aw rdata σ k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have hb := takeBuyerRepayment_bounds units buyerDebt
  have hr : (takeBuyerRepayment units buyerDebt).toNat < 2^128 := lt_of_le_of_lt hb.2 hd
  have hcalldata : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 68).toNat 32) =
      units := hunits
  have rd1 := midnight_block_12316 hstack (by jump_dest) rd
  simp only [midnight_block_12316_stack, hcalldata,
    uint128Mask_computed] at rd1
  obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedSub_mono
    (by simp only [List.length_cons]; omega) hb.1 (by jump_dest) rd1
  have rd3 := midnight_block_4204 (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  obtain ⟨k4, C4, hc4, rd4⟩ := midnightToUint128_mono
    (by simp only [List.length_cons]; omega) hr (by jump_dest) rd3
  have rd5 := midnight_block_6795 (by simp only [List.length_cons]; omega) (by jump_dest) rd4
  obtain ⟨k6, C6, hc6, rd6⟩ := midnightCheckedSub128_mono
    (by simp only [List.length_cons]; omega) hd hr hb.2 (by jump_dest) rd5
  exact ⟨k6, C6, by omega, rd6⟩

end Benchmarks.Midnight
