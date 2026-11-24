import Benchmarks.EAS.EAS.MemoryArrayIndex
import Benchmarks.EAS.EAS.RuntimeBlocks_031

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES the shared store-and-reindex suffix of easRecordArrayStore.
theorem easArrayStoreIndex {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i len : Nat}
    {array value ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+9 ≤ 1024) (hi : i < len)
    (hb : array.toNat+32+32*len < UInt256.size) (hin : array.toNat+32+32*len ≤ mem.size)
    (hl : memLoad array mem = UInt256.ofNat len)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5725⟩
      (array::UInt256.ofNat i::⟨9149⟩::value::array::UInt256.ofNat i::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (array.toNat+32+32*i)::R)
      (Reasoning.Theory.writeWord mem (array.toNat+32+32*i) value) aw' rdata σ k' C' := by
  have hcell : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i := ulit_toNat' _ (by omega)
  have hl' : memLoad array (Reasoning.Theory.writeWord mem (array.toNat+32+32*i) value) = UInt256.ofNat len :=
    (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans hl
  obtain ⟨aw1,k1,C1,rd1⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
    (by rw [easPatchedValidJumps v]; jump_dest) rd
  obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_9149_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  simp only [easBlocks.eas_block_9149_stack,easBlocks.eas_block_9149_memory,hcell] at rd2
  exact easMemoryArrayIndex v (by omega) hi (by omega) (by omega) hl' hret rd2

end Benchmarks.EAS.EAS
