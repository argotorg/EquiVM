import Benchmarks.Morpho.MetaMorphoV1_1.DomainMemory
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_064

/-! Bytecode allocation and hashing of the five-word domain preimage. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem domainHashRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 9 ≤ 1024)
    (hlo : 96 ≤ free) (hfit : free + 192 < 2 ^ 64)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13028⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (domainHash v I :: R)
      (domainHashMemory v I mem free) aw' rdata σ k' C' := by
  have hf (n : Nat) (hn : n ≤ 192) : free + n < UInt256.size := by
    change free + n < 2 ^ 256
    omega
  have hadd (n : Nat) (hn : n ≤ 192) :
      (UInt256.ofNat free + UInt256.ofNat n).toNat = free + n := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (hf n hn)]
  have ha : allocationFits (UInt256.ofNat free) (UInt256.ofNat 192) := by
    rw [allocationFits_iff_sum_lt]
    change (UInt256.ofNat free).toNat + 192 < 2 ^ 64
    rw [UInt256.toNat_ofNat_of_lt (by have := hf 0 (by omega); omega)]
    exact hfit
  have hnext : nextCursor (UInt256.ofNat free) (UInt256.ofNat 192) =
      UInt256.ofNat (free + 192) := by
    change UInt256.ofNat free + UInt256.ofNat 192 = _
    exact ofNat_add_words _ _
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_13028_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_13028_stack, hfree] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) ha
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have hm : writeWord (metaMorphoV1_1_block_13028_memory
      (immWords := wordsOf (immStore v)) (ee := I) (mem := mem))
      64 (nextCursor (UInt256.ofNat free) (UInt256.ofNat 192)) =
      domainHashMemory v I mem free := by
    simp only [metaMorphoV1_1_block_13028_memory, hfree, hnext,
      wordsOf_immStore__hashedName, wordsOf_immStore__hashedVersion,
      wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat,
      hadd 32 (by omega), hadd 64 (by omega), hadd 96 (by omega),
      hadd 128 (by omega), hadd 160 (by omega),
      UInt256.toNat_ofNat_of_lt (show free < UInt256.size by have := hf 0 (by omega); omega)]
    simp only [domainHashMemory, domainWords, wordSequenceMemory, domainTypeHash,
      Reasoning.Theory.writeWord, Nat.add_assoc]
    rfl
  rw [hm] at h2
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_13174_packed
    (immWords := wordsOf (immStore v)) (by omega) hret h2
  refine ⟨aw3, k3, C3, ?_⟩
  simp only [metaMorphoV1_1_block_13174_stack] at h3
  rw [domainHashMemory_length _ _ _ _ hlo
    (by have := hf 0 (by omega); omega)] at h3
  simp only [keccakWord, hadd 32 (by omega)] at h3
  change RD _ _ _ _ _
    (UInt256.ofNat (fromByteArrayBigEndian (KEC
      ((domainHashMemory v I mem free).readWithPadding (free + 32) 160))) :: R)
    _ _ _ _ _ _ at h3
  rw [domainHashMemory_read _ _ _ _ hlo] at h3
  simpa only [domainHash, uInt256OfByteArray_eq] using h3

end Benchmarks.Morpho.MetaMorphoV1_1
