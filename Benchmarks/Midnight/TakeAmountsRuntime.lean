import Benchmarks.Midnight.WmulUp
import Benchmarks.Midnight.TakeSpread
import Benchmarks.Midnight.RuntimeBlocks_054

variable {fork : Ethereum.Fork}

/-! Both asset calculations, with their multiplication and rounding overflow paths. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeAmount (buy units price : UInt256) : UInt256 :=
  if buy = ⟨0⟩ then mulDivUp units price takePriceScale
  else mulDivDown units price takePriceScale

def TakeAmountSafe (buy units price : UInt256) : Prop :=
  if buy = ⟨0⟩ then MulDivUpSafe units price takePriceScale
  else units.toNat * price.toNat < UInt256.size

def takeAmountMemory (mem : ByteArray) (off : Nat) (amount : UInt256) : ByteArray :=
  writeWord (writeWord mem off ⟨0⟩) off amount

theorem midnightTakeBuyerAmount {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw buy units price : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hbuy : memLoad (UInt256.ofNat 32 + memLoad (UInt256.ofNat 384) mem) mem = buy)
    (hunits : calldataWord I.calldata 68 = units) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11591⟩ (price :: R) mem aw rdata σ k C) :
    (¬ TakeAmountSafe buy units price ∧ RDrev fork midnightBytecode g s0) ∨
    (TakeAmountSafe buy units price ∧ ∃ aw' k' C',
      MemoryFunding credit (takeAmountMemory mem 256 (takeAmount buy units price)) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11636⟩ R
        (takeAmountMemory mem 256 (takeAmount buy units price)) aw' rdata σ k' C') := by
  by_cases hb : buy = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_11591_taken
      (by simp only [List.length_cons]; omega) (by rw [hbuy, hb]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_11591_taken_memory] at rd1
    have rd2 := midnightBlocks.midnight_block_14738 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_14738_stack] at rd2
    change RD fork midnightBytecode I g s0 ⟨24082⟩
      (calldataWord I.calldata 68 :: price :: UInt256.ofNat 14750 :: R) _ _ rdata σ _ _ at rd2
    rw [hunits] at rd2
    rcases midnightWmulUp hstack (by jump_dest) rd2 with
      ⟨hbad, hr⟩ | ⟨hsafe, k3, C3, hC3, rd3⟩
    · exact Or.inl ⟨by simpa only [TakeAmountSafe, if_pos hb] using hbad, hr⟩
    · have ha3 := ha2.mono hC3
      have rd4 := midnightBlocks.midnight_block_14750 (by omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_14750_memory,
        midnightBlocks.midnight_block_14750_stack] at rd4
      have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha3)
      refine Or.inr ⟨by simpa only [TakeAmountSafe, if_pos hb] using hsafe, ?_⟩
      simp only [takeAmount, if_pos hb]
      exact ⟨_, _, _, ha4, rd4⟩
  · have rd1 := midnightBlocks.midnight_block_11591_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hbuy]; exact isZero_eq_zero_of_ne hb) rd
    simp only [midnightBlocks.midnight_block_11591_fallthrough_memory] at rd1
    have rd2 := midnightBlocks.midnight_block_11610 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_11610_stack] at rd2
    change RD fork midnightBytecode I g s0 ⟨20413⟩
      (calldataWord I.calldata 68 :: price :: UInt256.ofNat 11630 :: takePriceScale :: R)
      _ _ rdata σ _ _ at rd2
    rw [hunits] at rd2
    by_cases hmul : units.toNat * price.toNat < UInt256.size
    · obtain ⟨k3, C3, hC3, rd3⟩ := midnightCheckedMul_mono
        (by simp only [List.length_cons]; omega) hmul (by jump_dest) rd2
      have ha3 := ha2.mono hC3
      have rd4 := midnightBlocks.midnight_block_11630 (by omega) rd3
      simp only [midnightBlocks.midnight_block_11630_memory,
        midnightBlocks.midnight_block_11630_stack] at rd4
      have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha3)
      refine Or.inr ⟨by simpa only [TakeAmountSafe, if_neg hb] using hmul, ?_⟩
      simp only [takeAmount, if_neg hb]
      exact ⟨_, _, _, ha4, rd4⟩
    · exact Or.inl ⟨by simpa only [TakeAmountSafe, if_neg hb] using hmul,
        midnightCheckedMulRevert (by simp only [List.length_cons]; omega) (by omega) rd2⟩

theorem midnightTakeSellerAmount {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw buy units price : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hbuy : memLoad (UInt256.ofNat 32 + memLoad (UInt256.ofNat 384) mem) mem = buy)
    (hunits : calldataWord I.calldata 68 = units) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11636⟩ (price :: R) mem aw rdata σ k C) :
    (¬ TakeAmountSafe buy units price ∧ RDrev fork midnightBytecode g s0) ∨
    (TakeAmountSafe buy units price ∧ ∃ aw' k' C',
      MemoryFunding credit (takeAmountMemory mem 416 (takeAmount buy units price)) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11681⟩ R
        (takeAmountMemory mem 416 (takeAmount buy units price)) aw' rdata σ k' C') := by
  by_cases hb : buy = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_11636_taken
      (by simp only [List.length_cons]; omega) (by rw [hbuy, hb]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_11636_taken_memory] at rd1
    have rd2 := midnightBlocks.midnight_block_14717 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_14717_stack] at rd2
    change RD fork midnightBytecode I g s0 ⟨24082⟩
      (calldataWord I.calldata 68 :: price :: UInt256.ofNat 14729 :: R) _ _ rdata σ _ _ at rd2
    rw [hunits] at rd2
    rcases midnightWmulUp hstack (by jump_dest) rd2 with
      ⟨hbad, hr⟩ | ⟨hsafe, k3, C3, hC3, rd3⟩
    · exact Or.inl ⟨by simpa only [TakeAmountSafe, if_pos hb] using hbad, hr⟩
    · have ha3 := ha2.mono hC3
      have rd4 := midnightBlocks.midnight_block_14729 (by omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_14729_memory,
        midnightBlocks.midnight_block_14729_stack] at rd4
      have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha3)
      refine Or.inr ⟨by simpa only [TakeAmountSafe, if_pos hb] using hsafe, ?_⟩
      simp only [takeAmount, if_pos hb]
      exact ⟨_, _, _, ha4, rd4⟩
  · have rd1 := midnightBlocks.midnight_block_11636_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hbuy]; exact isZero_eq_zero_of_ne hb) rd
    simp only [midnightBlocks.midnight_block_11636_fallthrough_memory] at rd1
    have rd2 := midnightBlocks.midnight_block_11655 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_11655_stack] at rd2
    change RD fork midnightBytecode I g s0 ⟨20413⟩
      (calldataWord I.calldata 68 :: price :: UInt256.ofNat 11675 :: takePriceScale :: R)
      _ _ rdata σ _ _ at rd2
    rw [hunits] at rd2
    by_cases hmul : units.toNat * price.toNat < UInt256.size
    · obtain ⟨k3, C3, hC3, rd3⟩ := midnightCheckedMul_mono
        (by simp only [List.length_cons]; omega) hmul (by jump_dest) rd2
      have ha3 := ha2.mono hC3
      have rd4 := midnightBlocks.midnight_block_11675 (by omega) rd3
      simp only [midnightBlocks.midnight_block_11675_memory,
        midnightBlocks.midnight_block_11675_stack] at rd4
      have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha3)
      refine Or.inr ⟨by simpa only [TakeAmountSafe, if_neg hb] using hmul, ?_⟩
      simp only [takeAmount, if_neg hb]
      exact ⟨_, _, _, ha4, rd4⟩
    · exact Or.inl ⟨by simpa only [TakeAmountSafe, if_neg hb] using hmul,
        midnightCheckedMulRevert (by simp only [List.length_cons]; omega) (by omega) rd2⟩

end Benchmarks.Midnight
