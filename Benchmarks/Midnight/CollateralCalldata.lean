import Benchmarks.Midnight.CollateralCalldataCopy
import Benchmarks.Midnight.AllocationArithmetic

/-! Allocation and decoding of one in-bounds collateral argument. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCollateralCalldata {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hhead : head.toNat + 128 ≤ I.calldata.size) (hsize : I.calldata.size < 2^255)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hptr : ptr.toNat < 2^64)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨18500⟩
      (head :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    (¬ ptr.toNat + 128 < 2^64 ∧ RDrev midnightBytecode g s0) ∨
    (¬ CollateralData.canonicalAt I.calldata head.toNat ∧ RDrev midnightBytecode g s0) ∨
    (ptr.toNat + 128 < 2^64 ∧ CollateralData.canonicalAt I.calldata head.toNat ∧ ∃ aw' k' C',
      RD midnightBytecode I g s0 ret (ptr :: R)
        (writeWordArray (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr.toNat
          (CollateralData.at I.calldata head.toNat).words) aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_18500_fallthrough (by omega)
    (solcDecodeLenCheckOk (head := head) (need := UInt256.ofNat 128)
      hhead (by omega) (lt_size_of_lt_sign hsize) (by decide)) rd
  have rd2 := midnightBlocks.midnight_block_18513 (by
    simp only [midnightBlocks.midnight_block_18500_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_18513_stack, hfree,
    midnightBlocks.midnight_block_18500_fallthrough_stack] at rd2
  have hp : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  by_cases hfit : ptr.toNat + 128 < 2^64
  · obtain ⟨aw3, k3, C3, rd3⟩ := midnightAllocate128
      (by simp only [List.length_cons]; omega)
      (allocationCheck_ok (by rw [hp]; exact hfit) (by rw [hp]; omega)) (by jump_dest) rd2
    rcases midnightCollateralCalldataCopy hstack (by change _ < 2^256; omega)
      (by change _ < 2^256; omega) hvalid rd3 with ⟨hbad, hr⟩ | ⟨hc, hret⟩
    · exact Or.inr (Or.inl ⟨hbad, hr⟩)
    · exact Or.inr (Or.inr ⟨hfit, hc, hret⟩)
  · left
    refine ⟨hfit, ?_⟩
    exact midnightAllocate128Revert (by simp only [List.length_cons]; omega)
      (allocationCheck_large (by rw [hp]; omega) (by rw [hp]; omega)) rd2

end Benchmarks.Midnight
