import Benchmarks.EAS.EAS.ScalarDecode
import Benchmarks.EAS.EAS.RuntimeBlocks_017

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- The arbitrary-pointer counterpart of the scalar ABI entry decoder.
theorem easCalldataAddress {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4309⟩ (ptr::ret::R) mem aw rdata σ k C) :
    if (calldataWord ee.calldata ptr.toNat).toNat < EVM.addressModulus then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (calldataWord ee.calldata ptr.toNat::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hc : (calldataWord ee.calldata ptr.toNat).toNat < EVM.addressModulus
  · rw [if_pos hc]
    obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_4309_fallthrough_packed (immWords := wordsOf (immStore v)) hstack
      (by
        change UInt256.sub (calldataWord ee.calldata ptr.toNat) (UInt256.land (calldataWord ee.calldata ptr.toNat) solcAddrMask) = ⟨0⟩
        rw [solcAddrMask_clean hc,u256_sub_self]) rd
    exact easBlocks.eas_block_4341_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hret h
  · rw [if_neg hc]
    have hm : calldataWord ee.calldata ptr.toNat ≠ UInt256.land (calldataWord ee.calldata ptr.toNat) solcAddrMask := by
      intro he
      exact hc (he ▸ solcAddrMask_result_canonical _)
    obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_4309_taken_packed (immWords := wordsOf (immStore v)) hstack
      (u256_sub_ne_zero_of_ne hm) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp only [easBlocks.eas_block_4309_taken_stack,List.length_cons]; omega) h

end Benchmarks.EAS.EAS
