import Benchmarks.EAS.EAS.DelegatedRevocationDecode
import Benchmarks.EAS.EAS.RuntimeBlocks_024
import Benchmarks.EAS.EAS.MultiRequestControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000
-- GENERALIZES easMultiRequestIndex to the compiler's 128-byte delegated tuple index routine.
theorem easDelegatedBatchIndex {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i n : Nat}
    {base ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hi : i<n) (hn : n < UInt256.size) (hb : base.toNat+32*i < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6041⟩
      (base::UInt256.ofNat n::UInt256.ofNat i::ret::R) mem aw rdata σ k C) :
    if delegatedBatchReferenceValid ee.calldata base i then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (multiRequestRoot ee.calldata base i::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hin : (UInt256.ofNat i).toNat = i := ulit_toNat' _ (by omega)
  have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) = UInt256.ofNat (32*i) :=
    shiftLeft5_ofNat_eq (by omega)
  have hslot : (base+UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat = base.toNat+32*i := by
    rw [hshift,uadd_word_ofNat_toNat _ _ hb]
  have hneg : (UInt256.sub (UInt256.ofNat ee.calldata.size) base)+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639809 =
      (UInt256.ofNat ee.calldata.size-base)-⟨127⟩ := by rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size-base) ⟨127⟩]; rfl
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6041_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ult_one (by rw [hin,ulit_toNat' _ hn]; exact hi)]; rfl) rd
  simp only [easBlocks.eas_block_6041_fallthrough_stack] at r1
  by_cases hv : delegatedBatchReferenceValid ee.calldata base i
  · rw [if_pos hv]
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_6051_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hslot,hneg]; exact hv) r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_6102_packed (immWords := wordsOf (immStore v)) (by omega) hret r2
    exact ⟨a3,k3,C3,by simpa only [easBlocks.eas_block_6102_stack,easBlocks.eas_block_6051_fallthrough_stack,
      hslot,multiRequestRoot] using r3⟩
  · rw [if_neg hv]
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_6051_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hslot,hneg]; exact hv)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_6051_taken_stack,List.length_cons]; omega) r2


end Benchmarks.EAS.EAS
