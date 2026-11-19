import Benchmarks.Midnight.CollateralCalldataAccounting
import Benchmarks.Midnight.CollateralLoopMemory

/-! One iteration of the market calldata collateral loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCollateralCalldataLoopStep_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head writePtr finish : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 18 ≤ 1024)
    (hhead : head.toNat + 128 ≤ I.calldata.size) (hsize : I.calldata.size < 2^255)
    (hmore : head.toNat + 128 ≤ finish.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hptr : ptr.toNat < 2^64)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18726⟩
      (writePtr :: UInt256.ofNat I.calldata.size :: head :: finish :: R) mem aw rdata σ k C) :
    (¬ ptr.toNat + 128 < 2^64 ∧ RDrev midnightBytecode g s0) ∨
    (¬ CollateralData.canonicalAt I.calldata head.toNat ∧ RDrev midnightBytecode g s0) ∨
    (ptr.toNat + 128 < 2^64 ∧ CollateralData.canonicalAt I.calldata head.toNat ∧ ∃ aw' k' C',
      MemoryAccounting
        (collateralStepMemory mem ptr writePtr (CollateralData.at I.calldata head.toNat)) aw' C' ∧
      RD midnightBytecode I g s0 ⟨18726⟩
        ((writePtr + UInt256.ofNat 32) :: UInt256.ofNat I.calldata.size ::
          (head + UInt256.ofNat 128) :: finish :: R)
        (collateralStepMemory mem ptr writePtr (CollateralData.at I.calldata head.toNat))
        aw' rdata σ k' C') := by
  have hc : UInt256.lt head finish = ⟨1⟩ := ult_one (by omega)
  have rd1 := midnightBlocks.midnight_block_18726_taken (by omega)
    (by rw [hc]; decide) (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_18793 (by
    simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_18793_stack] at rd2
  have ha2 := memoryAccountingAt rd2 (by memory_account ha)
  rcases midnightCollateralCalldata_accounted (by simp only [List.length_cons]; omega)
      hhead hsize hfree hptr (by jump_dest) ha2 rd2 with
    ⟨hbad, hr⟩ | ⟨hbad, hr⟩ | ⟨hfit, hcanon, aw3, k3, C3, ha3, rd3⟩
  · exact Or.inl ⟨hbad, hr⟩
  · exact Or.inr (Or.inl ⟨hbad, hr⟩)
  · right; right
    refine ⟨hfit, hcanon, ?_⟩
    have rd4 := midnightBlocks.midnight_block_18808 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd3
    have ha4 := memoryAccountingAt rd4 (by
      unfold midnightBlocks.midnight_block_18808_memory
      memory_account ha3)
    exact ⟨_, _, _, ha4, rd4⟩

end Benchmarks.Midnight
