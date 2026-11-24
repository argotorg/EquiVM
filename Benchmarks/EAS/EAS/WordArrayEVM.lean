import Benchmarks.EAS.EAS.TimestampEVM
import Benchmarks.EAS.EAS.WordArrayBase

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

/-- The common calldata word-array decoder, returning its length and first element address. -/
theorem easWordArrayDecode_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {start limit ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hheader : UInt256.isZero (UInt256.slt (start + UInt256.ofNat 31) limit) = ⟨0⟩)
    (hlength : UInt256.gt (calldataWord ee.calldata start.toNat) (UInt256.ofNat 18446744073709551615) = ⟨0⟩)
    (hextent : UInt256.gt (((UInt256.shiftLeft (calldataWord ee.calldata start.toNat) (UInt256.ofNat 5)) + start) + UInt256.ofNat 32) limit = ⟨0⟩)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4225⟩ (start :: limit :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork (deployedRuntime v) ee g s0 ret (calldataWord ee.calldata start.toNat :: (start + UInt256.ofNat 32) :: R)
      mem aw rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_4225_fallthrough (immWords := wordsOf (immStore v)) (by omega) hheader rd
  have rd2 := easBlocks.eas_block_4238_fallthrough (immWords := wordsOf (immStore v)) (by omega) hlength rd1
  have rd3 := easBlocks.eas_block_4256_fallthrough (immWords := wordsOf (immStore v)) hstack hextent rd2
  have rd4 := easBlocks.eas_block_4273 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hvalid rd3
  exact ⟨_, _, rd4⟩

/-- The shared indexed access routine; the caller's loop supplies its bounds proof. -/
theorem easWordArrayIndex_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {start length index ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 5 ≤ 1024) (hi : index.toNat < length.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5006⟩ (start :: length :: index :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork (deployedRuntime v) ee g s0 ret ((UInt256.shiftLeft index (UInt256.ofNat 5) + start) :: R)
      mem aw rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_5006_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ult_one hi]; decide) rd
  have rd2 := easBlocks.eas_block_5016 (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
  exact ⟨_, _, rd2⟩

theorem easWordArrayDecode_revert_header {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {start limit ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 6 ≤ 1024)
    (hheader : UInt256.isZero (UInt256.slt (start + UInt256.ofNat 31) limit) ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4225⟩ (start :: limit :: ret :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have rd1 := easBlocks.eas_block_4225_taken (immWords := wordsOf (immStore v)) hstack hheader
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_4225_taken_stack, List.length_cons]; omega) rd1

theorem easWordArrayDecode_revert_length {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {start limit ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 6 ≤ 1024)
    (hheader : UInt256.isZero (UInt256.slt (start + UInt256.ofNat 31) limit) = ⟨0⟩)
    (hlength : UInt256.gt (calldataWord ee.calldata start.toNat) (UInt256.ofNat 18446744073709551615) ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4225⟩ (start :: limit :: ret :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have rd1 := easBlocks.eas_block_4225_fallthrough (immWords := wordsOf (immStore v)) hstack hheader rd
  have rd2 := easBlocks.eas_block_4238_taken (immWords := wordsOf (immStore v)) hstack hlength
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_4238_taken_stack, List.length_cons]; omega) rd2

theorem easWordArrayDecode_revert_extent {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {start limit ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hheader : UInt256.isZero (UInt256.slt (start + UInt256.ofNat 31) limit) = ⟨0⟩)
    (hlength : UInt256.gt (calldataWord ee.calldata start.toNat) (UInt256.ofNat 18446744073709551615) = ⟨0⟩)
    (hextent : UInt256.gt (((UInt256.shiftLeft (calldataWord ee.calldata start.toNat) (UInt256.ofNat 5)) + start) + UInt256.ofNat 32) limit ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4225⟩ (start :: limit :: ret :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have rd1 := easBlocks.eas_block_4225_fallthrough (immWords := wordsOf (immStore v)) (by omega) hheader rd
  have rd2 := easBlocks.eas_block_4238_fallthrough (immWords := wordsOf (immStore v)) (by omega) hlength rd1
  have rd3 := easBlocks.eas_block_4256_taken (immWords := wordsOf (immStore v)) hstack hextent
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_4256_taken_stack, List.length_cons]; omega) rd3

end Benchmarks.EAS.EAS
