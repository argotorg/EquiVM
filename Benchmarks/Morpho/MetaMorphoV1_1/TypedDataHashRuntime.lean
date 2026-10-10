import Benchmarks.Morpho.MetaMorphoV1_1.TypedDataHashMemory
import Benchmarks.Morpho.MetaMorphoV1_1.DomainCacheRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! Runtime construction of the EIP-712 envelope before signature recovery. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem typedDataHashRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {domain structHash sigV : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 6 ≤ 1024)
    (hfit : free + 66 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (rd : RD (deployedRuntime v) I g s0 ⟨1792⟩ (domain :: structHash :: sigV :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨19083⟩
      (typedDataHash domain structHash :: sigV ::
        uInt256OfByteArray (I.calldata.readBytes 164 32) ::
        uInt256OfByteArray (I.calldata.readBytes 196 32) :: R)
      (typedDataHashMemory mem free domain structHash) aw' rdata σ k' C' := by
  have hf : free < UInt256.size := by omega
  have hadd (n : Nat) (hn : n ≤ 66) :
      (UInt256.ofNat free + UInt256.ofNat n).toNat = free + n := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  have hm : metaMorphoV1_1_block_1792_memory
      (mem := mem) (x0 := domain) (x1 := structHash) =
      typedDataHashMemory mem free domain structHash := by
    simp only [metaMorphoV1_1_block_1792_memory, hfree,
      UInt256.toNat_ofNat_of_lt hf, hadd 2 (by omega), hadd 34 (by omega),
      typedDataHashMemory, SourceMemory.wordPrefixMemory, wordSequenceMemory,
      Reasoning.Theory.writeWord, typedDataPrefixWord, Nat.add_assoc]
    rfl
  obtain ⟨aw', k', C', r⟩ := metaMorphoV1_1_block_1792_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD _ _ _ _ _
    (keccakWord (memLoad (UInt256.ofNat 64) mem) ⟨66⟩
      (metaMorphoV1_1_block_1792_memory (mem := mem) (x0 := domain) (x1 := structHash)) ::
      sigV :: uInt256OfByteArray (I.calldata.readBytes 164 32) ::
        uInt256OfByteArray (I.calldata.readBytes 196 32) :: R)
    (metaMorphoV1_1_block_1792_memory (mem := mem) (x0 := domain) (x1 := structHash))
    _ _ _ _ _ at r
  rw [hm, hfree] at r
  simp only [keccakWord, UInt256.toNat_ofNat_of_lt hf] at r
  change RD _ _ _ _ _
    (UInt256.ofNat (fromByteArrayBigEndian (KEC
      ((typedDataHashMemory mem free domain structHash).readWithPadding free 66))) ::
      sigV :: uInt256OfByteArray (I.calldata.readBytes 164 32) ::
        uInt256OfByteArray (I.calldata.readBytes 196 32) :: R) _ _ _ _ _ _ at r
  rw [typedDataHashMemory_read] at r
  exact ⟨aw', k', C', by simpa only [typedDataHash, uInt256OfByteArray_eq] using r⟩

end Benchmarks.Morpho.MetaMorphoV1_1
