import Benchmarks.EAS.EAS.GetAttestationReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the scratch mapping hash preserves the heap word.
theorem twoWordHashMem_heap (key slot heap : UInt256) (mem : ByteArray)
    (hin : 96 ≤ mem.size) (hh : memLoad (UInt256.ofNat 64) mem = heap) :
    memLoad (UInt256.ofNat 64) (twoWordHashMem key slot mem) = heap := by
  apply mloadWordValue_of_readWithPadding
  · rw [twoWordHashMem_size_of_ge_64 key slot (by omega)]
    change 64 < mem.size
    omega
  · change (twoWordHashMem key slot mem).readWithPadding 64 32 = heap.toByteArray
    rw [twoWordHashMem_read_above64 key slot 64 (by decide) hin,
      ← memLoad_bytes mem 64 (by decide) hin, hh]

theorem getAttestationEVM {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+17 ≤ 1024) (hh : memLoad ⟨64⟩ mem = ⟨224⟩)
    (rd : RD fork (deployedRuntime v) evm.executionEnv g s0 ⟨2593⟩ R mem aw rdata evm.accountMap k C) :
    if copyStoredValid evm (calldataWord evm.executionEnv.calldata 4) 544 then
      RDret fork (deployedRuntime v) g s0 evm.accountMap
        (attestationReturnBytes evm (calldataWord evm.executionEnv.calldata 4))
    else RDrev fork (deployedRuntime v) g s0 := by
  let word := calldataWord evm.executionEnv.calldata 4
  let m := defaultAttestationMemory mem ⟨224⟩
  have rd1 := easBlocks.eas_block_2593 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw1,k1,C1,rd2⟩ := easDefaultAttestation_ok v (by omega) hh (by decide)
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  have hmsz : 96 ≤ m.size := by
    have hg := writeWordSequence_grows (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat 544)) 224 defaultAttestationWords
    rw [writeWord_sparse_size] at hg
    exact le_trans (by omega) hg
  have hm64 : memLoad (UInt256.ofNat 64) m = UInt256.ofNat 544 :=
    defaultAttestationMemory_heap mem ⟨224⟩ (by decide)
  obtain ⟨aw2,k2,C2,rd3⟩ := easBlocks.eas_block_2600_packed (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hmem : easBlocks.eas_block_2600_memory (ee := evm.executionEnv) (mem := m) = twoWordHashMem word ⟨1⟩ m := rfl
  have hs : easBlocks.eas_block_2600_stack (ee := evm.executionEnv) (mem := m) (R := R) =
      dbSlot word :: UInt256.ofNat 2628 :: UInt256.ofNat 398 :: R := by
    change UInt256.ofNat (fromByteArrayBigEndian (KEC ((twoWordHashMem word ⟨1⟩ m).readWithPadding 0 64))) :: _ = _
    rw [twoWordHashMem_solcMappingSlot_any]
    rfl
  change RD fork (deployedRuntime v) evm.executionEnv g s0 (UInt256.ofNat 6501)
    (easBlocks.eas_block_2600_stack (ee := evm.executionEnv) (mem := m) (R := R))
    (easBlocks.eas_block_2600_memory (ee := evm.executionEnv) (mem := m)) aw2 rdata evm.accountMap k2 C2 at rd3
  rw [hmem, hs] at rd3
  have hc := easCopyStored v (heap := UInt256.ofNat 544) (by simp only [List.length_cons]; omega)
    (twoWordHashMem_heap word ⟨1⟩ (UInt256.ofNat 544) m hmsz hm64) (by decide)
    (by rw [easPatchedValidJumps v]; jump_dest) rd3
  simp only [show (UInt256.ofNat 544).toNat = 544 from rfl] at hc
  by_cases hv : copyStoredValid evm word 544
  · rw [if_pos hv] at hc
    obtain ⟨aw3,k3,C3,rd4⟩ := hc
    rw [if_pos hv]
    exact getAttestationReturnEVM (heap := UInt256.ofNat 544) (word := word) v hstack (by decide) hv rd4
  · rw [if_neg hv] at hc
    rw [if_neg hv]
    exact hc

end Benchmarks.EAS.EAS
