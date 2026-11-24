import Benchmarks.EAS.EAS.BytesAllocation

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the compiler's masked byte-array allocation size equals the source formula.
theorem bytesAllocation_word (size : UInt256) (hb : size.toNat ≤ 2^64-1) :
    (⟨32⟩ : UInt256) + UInt256.land (UInt256.lnot ⟨31⟩) ((⟨31⟩ : UInt256)+size) =
      UInt256.ofNat (bytesAllocation size.toNat) := by
  rw [u256_land_comm, u256_add_comm (⟨31⟩ : UInt256), allocateNext_word]
  apply congrArg UInt256.ofNat
  have h1 : size.toNat+31 < UInt256.size := by change size.toNat+31 < 2^256; omega
  have h2 : 32+(size.toNat+31)/32*32 < UInt256.size := by change 32+(size.toNat+31)/32*32 < 2^256; omega
  simp only [allocateNext, allocateRounded, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, bytesAllocation]
  exact Nat.mod_eq_of_lt h2

theorem easBytesAllocation {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {size ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+4 ≤ 1024) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4948⟩ (size::ret::R) mem aw rdata σ k C) :
    if size.toNat ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (bytesAllocation size.toNat)::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hb : size.toNat ≤ 2^64-1
  · rw [if_pos hb]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_4948_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (ugt_zero hb) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_4964_packed (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
    refine ⟨aw2,k2,C2,?_⟩
    simpa only [easBlocks.eas_block_4964_stack, show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from rfl,
      show UInt256.ofNat 31 = (⟨31⟩ : UInt256) from rfl,
      show UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 = UInt256.lnot ⟨31⟩ from rfl,
      bytesAllocation_word size hb] using rd2
  · rw [if_neg hb]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_4948_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [ugt_one (by change 18446744073709551615 < size.toNat; omega)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_4723 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd1

end Benchmarks.EAS.EAS
