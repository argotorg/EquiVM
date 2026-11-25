import Benchmarks.Midnight.ToMarketCollateral
import Benchmarks.Midnight.AllocationArithmetic

variable {fork : Ethereum.Fork}

/-! One iteration of collateral allocation, decoding, and pointer-array construction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def collateralStepMemory (mem : ByteArray) (ptr writePtr : UInt256) (c : CollateralData) : ByteArray :=
  collateralCopyMemory (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr writePtr c

theorem midnightToMarketLoopStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr readPtr writePtr x finish : UInt256} {σ : AccountMap}
    {base start k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hbytes : MemoryBytes mem base bytes) (hbase : 96 ≤ base)
    (hhead : start + 128 ≤ bytes.size) (hread : readPtr.toNat = base + start)
    (hend : x.toNat + 32 = base + bytes.size) (hsmall : base + bytes.size < 2^128)
    (hmore : readPtr.toNat + 128 ≤ finish.toNat)
    (hregion : base + bytes.size ≤ ptr.toNat) (hptr : ptr.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork midnightBytecode I g s0 ⟨1092⟩ (writePtr :: x :: finish :: readPtr :: R)
      mem aw rdata σ k C) :
    (¬ ptr.toNat + 128 < 2^64 ∧ RDrev fork midnightBytecode g s0) ∨
    (¬ CollateralData.canonicalAt bytes start ∧ RDrev fork midnightBytecode g s0) ∨
    (ptr.toNat + 128 < 2^64 ∧ CollateralData.canonicalAt bytes start ∧
      ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨1092⟩
        ((writePtr + UInt256.ofNat 32) :: x :: finish :: (readPtr + UInt256.ofNat 128) :: R)
        (collateralStepMemory mem ptr writePtr (CollateralData.at bytes start)) aw' rdata σ k' C') := by
  have hlt : UInt256.lt readPtr finish = ⟨1⟩ := ult_one (by omega)
  have rd1 := midnightBlocks.midnight_block_1092_taken (by omega)
    (by rw [hlt]; decide) (by jump_dest) rd
  have hs : (UInt256.sub x readPtr).toNat = x.toNat - readPtr.toNat := usub_toNat (by omega)
  have hsum : ((UInt256.sub x readPtr) + UInt256.ofNat 32).toNat =
      x.toNat - readPtr.toNat + 32 := by
    rw [uadd_word_ofNat_toNat _ _ (by rw [hs]; change _ < 2^256; omega), hs]
  have hc : UInt256.slt ((UInt256.sub x readPtr) + UInt256.ofNat 32) (UInt256.ofNat 128) =
      ⟨0⟩ := slt_lit_zero (by decide) (by rw [hsum]; omega) (by rw [hsum]; omega)
  have rd2 := midnightBlocks.midnight_block_1188_fallthrough (by omega) hc rd1
  have rd3 := midnightBlocks.midnight_block_1202
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_1202_stack, hfree] at rd3
  have hp128 : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  by_cases hfit : ptr.toNat + 128 < 2^64
  · have halloc : allocationCheck ptr (ptr + UInt256.ofNat 128) = ⟨0⟩ :=
      allocationCheck_ok (by rw [hp128]; exact hfit) (by rw [hp128]; omega)
    obtain ⟨aw4, k4, C4, rd4⟩ := midnightAllocate128
      (by simp only [List.length_cons]; omega) halloc (by jump_dest) rd3
    have hb : MemoryBytes (writeWord mem 64 (ptr + UInt256.ofNat 128)) base bytes :=
      hbytes.writeWord _ (Or.inr hbase)
    rcases midnightToMarketCollateral (by omega) hb hhead hread hregion hfit rd4 with
      ⟨hnc, hrev⟩ | ⟨hcanon, aw5, k5, C5, rd5⟩
    · exact Or.inr (Or.inl ⟨hnc, hrev⟩)
    · exact Or.inr (Or.inr ⟨hfit, hcanon, aw5, k5, C5, rd5⟩)
  · left
    refine ⟨hfit, ?_⟩
    exact midnightAllocate128Revert (by simp only [List.length_cons]; omega)
      (allocationCheck_large (by rw [hp128]; omega) (by rw [hp128]; omega)) rd3

end Benchmarks.Midnight
