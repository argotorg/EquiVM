import Benchmarks.Morpho.MetaMorphoV1_1.StringReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_016
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_024

/-! The shared runtime encoder for storage-backed string getters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem stringReturnRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (len : UInt256) (bytes : ByteArray) (free : Nat)
    (hstack : R.length + 10 ≤ 1024) (hlen : len.toNat < 2 ^ 255)
    (hfree : 160 + len.toNat ≤ free)
    (hfit : free + 64 + ABI.paddedSize len.toNat + 32 < UInt256.size)
    (hmem : 160 + len.toNat ≤ mem.size)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hload : memLoad ⟨128⟩ mem = len)
    (hsize : bytes.size = len.toNat) (hdata : mem.readWithPadding 160 len.toNat = bytes)
    (rd : RD (deployedRuntime v) I g s0 ⟨2379⟩ (⟨128⟩ :: ⟨4335⟩ :: R)
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (stringReturnBytes bytes) := by
  have hf : free < UInt256.size := by omega
  have hfout : free + 64 + ABI.paddedSize len.toNat < UInt256.size := by omega
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2379_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_2379_stack, metaMorphoV1_1_block_2379_memory, hptr,
    UInt256.toNat_ofNat_of_lt hf] at h1
  have hl : memLoad ⟨128⟩ ((UInt256.ofNat 32).toByteArray.write 0 mem free 32) = len := by
    rw [memLoad_write_disjoint _ _ _ _ (by change 160 ≤ mem.size; omega)
      (.inl (by change 160 ≤ free; omega)), hload]
  rw [ofNat_add_words] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := stringEncoderRoutine v 128 (free + 32) len
    (by simp only [List.length_cons]; omega) hlen (by decide) hfit hl
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  change RD _ I g s0 ⟨4335⟩
    (UInt256.ofNat (free + 64 + ABI.paddedSize len.toNat) :: UInt256.ofNat free ::
      UInt256.ofNat free :: R)
    (stringReturnMemory mem 160 free len) aw2 rdata σ k2 C2 at h2
  have hret := metaMorphoV1_1_block_4335 (immWords := wordsOf (immStore v)) (by omega) h2
  have hdiff : (UInt256.sub (UInt256.ofNat (free + 64 + ABI.paddedSize len.toNat))
      (UInt256.ofNat free)).toNat = 64 + ABI.paddedSize len.toNat := by
    rw [usub_toNat (by rw [UInt256.toNat_ofNat_of_lt hf,
      UInt256.toNat_ofNat_of_lt hfout]; omega), UInt256.toNat_ofNat_of_lt hf,
      UInt256.toNat_ofNat_of_lt hfout]
    omega
  simpa only [UInt256.toNat_ofNat_of_lt hf, hdiff,
    stringReturnMemory_read mem bytes 160 free len hsize hmem hfree hdata] using hret

end Benchmarks.Morpho.MetaMorphoV1_1
