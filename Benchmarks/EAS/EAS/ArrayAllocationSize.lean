import Benchmarks.EAS.EAS.Allocate
import Benchmarks.EAS.EAS.RuntimeBlocks_020

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easArrayAllocationSize {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {len ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5069⟩ (len::ret::R) mem aw rdata σ k C) :
    if len.toNat ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (32+32*len.toNat)::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hl : len.toNat ≤ 2^64-1
  · rw [if_pos hl]
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5069_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (ugt_zero (by exact hl)) rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5085_packed (immWords := wordsOf (immStore v)) (by omega) hret r1
    have he : UInt256.shiftLeft len (UInt256.ofNat 5) = UInt256.ofNat (32*len.toNat) := by
      conv_lhs => rw [← u256_ofNat_toNat len]
      exact shiftLeft5_ofNat_eq (by change 32*len.toNat < 2^256; omega)
    refine ⟨a2,k2,C2,?_⟩
    simpa only [easBlocks.eas_block_5085_stack,he,show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from rfl,
      u256_32_add_ofNat,Nat.add_comm] using r2
  · rw [if_neg hl]
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5069_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [ugt_one (by change 18446744073709551615 < len.toNat; omega)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_4723 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) r1

end Benchmarks.EAS.EAS
