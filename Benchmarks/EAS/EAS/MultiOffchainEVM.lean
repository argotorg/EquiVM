import Benchmarks.EAS.EAS.TimeArrayEVM
import Benchmarks.EAS.EAS.OffchainEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easMultiOffchain_call {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {i length start time : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 14 ≤ 1024) (hi : i.toNat < length.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4089⟩ (i :: length :: start :: time :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork (deployedRuntime v) ee g s0 ⟨7001⟩
      (keyValueToWord (.address ee.source) :: timeArrayWord ee start i :: time :: ⟨4132⟩ :: i :: ⟨1⟩ :: length :: start :: time :: R)
      mem aw rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_4089_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ult_one hi]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  have rd2 := easBlocks.eas_block_4107 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  obtain ⟨k3, C3, rd3⟩ := easWordArrayIndex_ok (start := start) (length := length) (index := i) (ret := ⟨4125⟩) v
    (by simp only [List.length_cons]; omega) hi (by rw [easPatchedValidJumps v]; jump_dest) rd2
  have rd4 := easBlocks.eas_block_4125 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
  exact ⟨_, _, by simpa only [easBlocks.eas_block_4125_stack, keyValueToWord_address] using rd4⟩

theorem easMultiOffchain_step {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {i length start time : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 14 ≤ 1024) (hi : i.toNat < length.toNat)
    (hz : UInt256.land (solcSlotWord σ ee (offchainSlot (keyValueToWord (.address ee.source)) (timeArrayWord ee start i))) easUint64Mask = ⟨0⟩)
    (hp : ee.perm = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4089⟩ (i :: length :: start :: time :: R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4089⟩ ((i + ⟨1⟩) :: length :: start :: time :: R)
      mem' aw' rdata (offchainAccounts σ ee ee.source (timeArrayWord ee start i) time) k' C' := by
  obtain ⟨k1, C1, rd1⟩ := easMultiOffchain_call v hstack hi rd
  obtain ⟨aw2, k2, C2, rd2⟩ := easOffchain_ok v (revoker := ee.source)
    (word := timeArrayWord ee start i) (time := time) (ret := ⟨4132⟩)
    (by simp only [List.length_cons]; omega) hz hp (by rw [easPatchedValidJumps v]; jump_dest) rd1
  have rd3 := easBlocks.eas_block_4132 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨_, _, _, _, rd3⟩

theorem easMultiOffchain_end {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {i length start time : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024) (hi : length.toNat ≤ i.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4089⟩ (i :: length :: start :: time :: R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ time.toByteArray := by
  have rd1 := easBlocks.eas_block_4089_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (ult_zero hi) rd
  have hr := easBlocks.eas_block_4097 (immWords := wordsOf (immStore v)) hstack rd1
  rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
    ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
  exact hr

end Benchmarks.EAS.EAS
