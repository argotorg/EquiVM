import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ScalarDecode

variable {fork : Ethereum.Fork}

/-! Shared address-validation routines in Midnight's runtime. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000

theorem addressMask_computed :
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by native_decide

theorem addressCheck_zero {word : UInt256} (hcanon : word.toNat < EVM.addressModulus) :
    UInt256.sub word (UInt256.land word
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))) = UInt256.ofNat 0 := by
  rw [addressMask_computed, solcAddrMask_clean hcanon]
  exact u256_sub_eq_zero_iff_eq.mpr rfl

theorem addressCheck_nonzero {word : UInt256} (hnc : ¬ word.toNat < EVM.addressModulus) :
    UInt256.sub word (UInt256.land word
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
  rw [addressMask_computed]
  intro h
  have heq := u256_sub_eq_zero_iff_eq.mp h
  apply hnc
  simpa only [← heq] using solcAddrMask_result_canonical word

theorem midnightAddress4_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode ee g s0 (UInt256.ofNat 18254) (ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18254_fallthrough hstack
    (addressCheck_zero hcanon) rd
  have rd2 := midnightBlocks.midnight_block_18275 (by
    simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, rd2⟩

theorem midnightAddress4_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hnc : ¬ (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode ee g s0 (UInt256.ofNat 18254) (ret :: R)
      mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_18254_taken hstack
    (addressCheck_nonzero hnc) (by jump_dest) rd
  exact midnightBlocks.midnight_block_6350 (by
    simp only [midnightBlocks.midnight_block_18254_taken_stack, List.length_cons]; omega) rd1

theorem midnightAddress36_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (hcanon : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode ee g s0 (UInt256.ofNat 18232) (ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode ee g s0 ret (calldataWord ee.calldata 36 :: R)
      mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18232_fallthrough hstack
    (addressCheck_zero hcanon) rd
  have rd2 := midnightBlocks.midnight_block_18253 (by
    simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, rd2⟩

theorem midnightAddress36_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hnc : ¬ (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode ee g s0 (UInt256.ofNat 18232) (ret :: R)
      mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_18232_taken hstack
    (addressCheck_nonzero hnc) (by jump_dest) rd
  exact midnightBlocks.midnight_block_6350 (by
    simp only [midnightBlocks.midnight_block_18232_taken_stack, List.length_cons]; omega) rd1

theorem midnightAddress68_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (hcanon : (calldataWord ee.calldata 68).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode ee g s0 (UInt256.ofNat 18276) (ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode ee g s0 ret (calldataWord ee.calldata 68 :: R)
      mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18276_fallthrough hstack
    (addressCheck_zero hcanon) rd
  have rd2 := midnightBlocks.midnight_block_18297 (by
    simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, rd2⟩

theorem midnightAddress68_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hnc : ¬ (calldataWord ee.calldata 68).toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode ee g s0 (UInt256.ofNat 18276) (ret :: R)
      mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_18276_taken hstack
    (addressCheck_nonzero hnc) (by jump_dest) rd
  exact midnightBlocks.midnight_block_6350 (by
    simp only [midnightBlocks.midnight_block_18276_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
