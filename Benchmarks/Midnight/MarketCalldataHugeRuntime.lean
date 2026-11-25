import Benchmarks.Midnight.MarketCalldataPrepare

variable {fork : Ethereum.Fork}

/-! Oversized calldata is rejected by the runtime market decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size) (hhuge : 2^255 ≤ I.calldata.size)
    (hhead : head.toNat < 2^127) (hptr : ptr.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork midnightBytecode I g s0 ⟨18574⟩
      (head :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  by_cases hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) head)
      (UInt256.ofNat 256) = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_18574_fallthrough (by omega) hcheck rd
    rcases midnightMarketCalldataPrepare hstack (by change _ < 2^256; omega)
        hptr hfree rd1 with
      ⟨_, hr⟩ | ⟨_, hr⟩ | ⟨_, _, _, hoff, aw2, k2, C2, rd2⟩
    · exact hr
    · exact hr
    · have ht : (head + calldataWord I.calldata (head.toNat + 96)).toNat =
          head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat := by
        rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
      have hs : UInt256.slt
          ((head + calldataWord I.calldata (head.toNat + 96)) + UInt256.ofNat 31)
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
        apply slt_zero_low_high
        · rw [uadd_word_ofNat_toNat _ _ (by rw [ht]; change _ < 2^256; omega), ht]
          omega
        · rw [UInt256.toNat_ofNat_of_lt hsize]
          exact hhuge
      have rd3 := midnightBlocks.midnight_block_18661_taken
        (by simp only [List.length_cons]; omega) (by rw [hs]; decide) (by jump_dest) rd2
      exact midnightBlocks.midnight_block_6350 (by
        simp only [midnightBlocks.midnight_block_18661_taken_stack, List.length_cons]; omega) rd3
  · have rd1 := midnightBlocks.midnight_block_18574_taken (by omega) hcheck (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by
      simp only [midnightBlocks.midnight_block_18574_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
