import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueClearLoop
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStorageMatch
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_049
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayRoutines

/-! Store the new length and clear exactly the obsolete queue suffix. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem supplyQueueStoreGuards {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C n : Nat}
    {index : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024) (hlen : n ≤ 30)
    (rd : RD (deployedRuntime v) I g s0 ⟨10063⟩
      (index :: UInt256.ofNat n :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨10089⟩ (UInt256.ofNat n :: R)
      mem aw out σ k' C' := by
  have hn : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (by
    have h : 30 < UInt256.size := by decide
    omega)
  have h1 := metaMorphoV1_1_block_10063_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      apply ugt_zero
      change (UInt256.ofNat n).toNat ≤ 18446744073709551615
      rw [hn]; omega) rd
  exact RD.pack (metaMorphoV1_1_block_10078_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by
      apply ugt_zero
      change (UInt256.ofNat n).toNat ≤ 18446744073709551616
      rw [hn]; omega) h1)

theorem supplyQueuePrepareStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C n : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = true) (hlen : n ≤ 30) (hmem : mem.size = 96)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨10089⟩ (UInt256.ofNat n :: R)
      mem aw out σ k C) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ((codeOwnerStorageWord I σ ⟨20⟩).toNat < 2 ^ 251 ∧
      ∃ junk mem', mem'.size = 96 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨10103⟩ (junk :: UInt256.ofNat n :: R)
        mem' aw' out
        (clearDataWordsForwardFrom I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨20⟩
          (UInt256.ofNat n)) (solidityBytesDataBaseSlot ⟨20⟩ + UInt256.ofNat n) ⟨0⟩
          ((codeOwnerStorageWord I σ ⟨20⟩).toNat - n)) k' C') := by
  let old := codeOwnerStorageWord I σ ⟨20⟩
  have hn : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (by
    have h : 30 < UInt256.size := by decide
    omega)
  by_cases hlt : n < old.toNat
  case neg =>
    obtain ⟨k1, C1, h1⟩ := metaMorphoV1_1_block_10089_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hperm (by
        apply ult_zero
        change old.toNat ≤ (UInt256.ofNat n).toNat
        rw [hn]; omega) rd
    refine .inr ⟨by change old.toNat < 2 ^ 251; omega, old, mem, hmem, hfree, aw, k1, C1, ?_⟩
    simpa only [show (codeOwnerStorageWord I σ ⟨20⟩).toNat - n = 0 by
      change old.toNat - n = 0; omega, clearDataWordsForwardFrom] using h1
  obtain ⟨k1, C1, h1⟩ := metaMorphoV1_1_block_10089_taken
    (immWords := wordsOf (immStore v)) (by omega) hperm (by
      have hword : (UInt256.ofNat n).toNat < old.toNat := by rw [hn]; exact hlt
      change UInt256.lt (UInt256.ofNat n) old ≠ UInt256.ofNat 0
      rw [ult_one hword]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_10264 (immWords := wordsOf (immStore v)) (by omega) h1
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 32) (wordAt0Mem ⟨20⟩ mem) =
      solidityBytesDataBaseSlot ⟨20⟩ := arrayScratchHash _ _
  simp only [metaMorphoV1_1_block_10264_stack, metaMorphoV1_1_block_10264_memory] at h2
  change RD _ _ _ _ _ ([⟨0⟩, keccakWord ⟨0⟩ (UInt256.ofNat 32) (wordAt0Mem ⟨20⟩ mem) +
    UInt256.ofNat n, UInt256.sub old (UInt256.ofNat n), UInt256.ofNat n] ++ R)
    (wordAt0Mem ⟨20⟩ mem) _ _ _ _ _ at h2
  rw [hh] at h2
  have hcount : (UInt256.sub old (UInt256.ofNat n)).toNat = old.toNat - n := by
    rw [usub_toNat (by rw [hn]; omega), hn]
  by_cases hsmall : old.toNat < 2 ^ 251
  · obtain ⟨k3, C3, _, h3⟩ := supplyQueueClearLoop v (old.toNat - n)
      (by change (UInt256.ofNat n :: R).length + 6 ≤ 1024
          simpa only [List.length_cons, Nat.add_assoc] using hstack) hperm
      (i := 0) (by rw [hcount]; omega) h2
    have h4 := metaMorphoV1_1_block_10288 (immWords := wordsOf (immStore v))
      (by change (_ :: _ :: R).length + 2 ≤ 1024; simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    exact .inr ⟨hsmall, _, _, wordAt0Mem_size_96 _ hmem,
      wordAt0Mem_read64 _ hmem hfree, _, _, _, h4⟩
  · exact .inl (supplyQueueClearLoopHuge v
      (by change (UInt256.ofNat n :: R).length + 6 ≤ 1024
          simpa only [List.length_cons, Nat.add_assoc] using hstack) hperm
      (by rw [hcount]; omega) h2)

end Benchmarks.Morpho.MetaMorphoV1_1
