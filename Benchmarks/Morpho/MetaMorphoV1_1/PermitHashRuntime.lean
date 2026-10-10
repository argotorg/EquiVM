import Benchmarks.Morpho.MetaMorphoV1_1.PermitHashMemory
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! Allocate and hash the six-word permit preimage in the deployed bytecode. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem permitStructHashRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value nonce deadline : UInt256}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (free : Nat)
    (hstack : R.length + 8 ≤ 1024) (hlo : 96 ≤ free) (hfit : free + 224 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨1762⟩
      (deadline :: UInt256.ofNat free :: UInt256.ofNat (free + 32) :: R)
      (permitHashPrefixMemory mem free owner spender value nonce) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12937⟩
      (⟨1792⟩ :: permitStructHash owner spender value nonce deadline :: R)
      (permitHashMemory mem free owner spender value nonce deadline) aw' rdata σ k' C' := by
  have hf : free < UInt256.size := by change free < 2 ^ 256; omega
  have hadd (n : Nat) (hn : n ≤ 224) :
      (UInt256.ofNat free + UInt256.ofNat n).toNat = free + n := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by change free + n < 2 ^ 256; omega)]
  have ha : allocationFits (UInt256.ofNat free) ⟨224⟩ := by
    rw [allocationFits_iff_sum_lt]
    change (UInt256.ofNat free).toNat + 224 < 2 ^ 64
    rw [UInt256.toNat_ofNat_of_lt hf]
    exact hfit
  have hn : nextCursor (UInt256.ofNat free) ⟨224⟩ = UInt256.ofNat (free + 224) := by
    change UInt256.ofNat free + UInt256.ofNat 224 = _
    exact ofNat_add_words _ _
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_1762_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_1762_stack] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) ha
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  have hm : writeWord (metaMorphoV1_1_block_1762_memory
      (mem := permitHashPrefixMemory mem free owner spender value nonce)
      (x0 := deadline) (x1 := UInt256.ofNat free))
      64 (nextCursor (UInt256.ofNat free) ⟨224⟩) =
      permitHashMemory mem free owner spender value nonce deadline := by
    simp only [metaMorphoV1_1_block_1762_memory, hn, hadd 192 (by omega),
      UInt256.toNat_ofNat_of_lt hf]
    exact permitHashMemory_finish _ _ _ _ _ _ _
  rw [hm] at r2
  obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_1781_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [metaMorphoV1_1_block_1781_stack] at r3
  rw [permitHashMemory_length _ _ _ _ _ _ _ hlo hf] at r3
  simp only [keccakWord, UInt256.toNat_ofNat_of_lt
    (show free + 32 < UInt256.size by change free + 32 < 2 ^ 256; omega)] at r3
  change RD _ _ _ _ _
    (⟨1792⟩ :: UInt256.ofNat (fromByteArrayBigEndian (KEC
      ((permitHashMemory mem free owner spender value nonce deadline).readWithPadding
        (free + 32) 192))) :: R) _ _ _ _ _ _ at r3
  rw [permitHashMemory_read _ _ _ _ _ _ _ hlo] at r3
  exact ⟨aw3, k3, C3, by simpa only [permitStructHash, uInt256OfByteArray_eq] using r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
