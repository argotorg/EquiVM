import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueClearLoop
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueHeap
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueStorage
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_041

/-! Queue-length guards, the header write, and cleanup of the obsolete storage suffix. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueStoreGuards {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C n : Nat}
    {a b c ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024) (hlen : n < 2 ^ 64)
    (hload : memLoad ptr mem = UInt256.ofNat n)
    (rd : RD (deployedRuntime v) I g s0 ⟨8183⟩
      (a :: b :: c :: ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8213⟩
      (UInt256.ofNat n :: ptr :: R) mem aw' out σ k' C' := by
  have hn : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (by
    exact lt_trans hlen (by decide))
  have r1 := metaMorphoV1_1_block_8183_fallthrough (immWords := wordsOf (immStore v))
    hstack (by
      rw [hload]
      apply ugt_zero
      change (UInt256.ofNat n).toNat ≤ 18446744073709551615
      rw [hn]; omega) rd
  simp only [metaMorphoV1_1_block_8183_fallthrough_stack, hload] at r1
  have r2 := metaMorphoV1_1_block_8202_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by
      apply ugt_zero
      change (UInt256.ofNat n).toNat ≤ 18446744073709551616
      rw [hn]; omega) r1
  exact ⟨_, _, _, r2⟩

theorem updateWithdrawQueuePrepareStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C curr n : Nat}
    {seen : List Bool} {queue : List UInt256} {cursor : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = true) (hm : UpdateWithdrawQueueHeap mem curr n seen queue cursor)
    (rd : RD (deployedRuntime v) I g s0 ⟨8213⟩ (UInt256.ofNat n :: R)
      mem aw out σ k C) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ((codeOwnerStorageWord I σ ⟨21⟩).toNat < 2 ^ 251 ∧
      ∃ junk mem', UpdateWithdrawQueueHeap mem' curr n seen queue cursor ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8227⟩ (junk :: UInt256.ofNat n :: R)
        mem' aw' out
        (clearDataWordsForwardFrom I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨21⟩
          (UInt256.ofNat n)) (solidityBytesDataBaseSlot ⟨21⟩ + UInt256.ofNat n) ⟨0⟩
          ((codeOwnerStorageWord I σ ⟨21⟩).toNat - n)) k' C') := by
  let old := codeOwnerStorageWord I σ ⟨21⟩
  have hlen : n < 2 ^ 64 := by have := hm.cursorLo; have := hm.cursorHi; omega
  have hn : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (lt_trans hlen (by decide))
  by_cases hlt : n < old.toNat
  case neg =>
    obtain ⟨k1, C1, r1⟩ := metaMorphoV1_1_block_8213_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hperm (by
        apply ult_zero
        change old.toNat ≤ (UInt256.ofNat n).toNat
        rw [hn]; omega) rd
    refine .inr ⟨by change old.toNat < 2 ^ 251; omega, old, mem, hm, aw, k1, C1, ?_⟩
    simpa only [show (codeOwnerStorageWord I σ ⟨21⟩).toNat - n = 0 by
      change old.toNat - n = 0; omega, clearDataWordsForwardFrom] using r1
  obtain ⟨k1, C1, r1⟩ := metaMorphoV1_1_block_8213_taken
    (immWords := wordsOf (immStore v)) (by omega) hperm (by
      have hword : (UInt256.ofNat n).toNat < old.toNat := by rw [hn]; exact hlt
      change UInt256.lt (UInt256.ofNat n) old ≠ UInt256.ofNat 0
      rw [ult_one hword]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have r2 := metaMorphoV1_1_block_8392 (immWords := wordsOf (immStore v)) (by omega) r1
  simp only [metaMorphoV1_1_block_8392_stack, metaMorphoV1_1_block_8392_memory] at r2
  change RD _ _ _ _ _ ([⟨0⟩, keccakWord ⟨0⟩ (UInt256.ofNat 32) (wordAt0Mem ⟨21⟩ mem) +
    UInt256.ofNat n, UInt256.sub old (UInt256.ofNat n), UInt256.ofNat n] ++ R)
    (wordAt0Mem ⟨21⟩ mem) _ _ _ _ _ at r2
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 32) (wordAt0Mem ⟨21⟩ mem) =
      solidityBytesDataBaseSlot ⟨21⟩ := arrayScratchHash _ _
  rw [hh] at r2
  have hcount : (UInt256.sub old (UInt256.ofNat n)).toNat = old.toNat - n := by
    rw [usub_toNat (by rw [hn]; omega), hn]
  by_cases hsmall : old.toNat < 2 ^ 251
  · obtain ⟨k3, C3, _, r3⟩ := updateWithdrawQueueClearLoop v (old.toNat - n)
      (by change (UInt256.ofNat n :: R).length + 6 ≤ 1024
          simpa only [List.length_cons, Nat.add_assoc] using hstack) hperm
      (i := 0) (by rw [hcount]; omega) r2
    have r4 := metaMorphoV1_1_block_8416 (immWords := wordsOf (immStore v))
      (by change (_ :: _ :: R).length + 2 ≤ 1024; simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
    exact .inr ⟨hsmall, _, _, hm.scratch ⟨21⟩, _, _, _, r4⟩
  · exact .inl (updateWithdrawQueueClearLoopHuge v
      (by change (UInt256.ofNat n :: R).length + 6 ≤ 1024
          simpa only [List.length_cons, Nat.add_assoc] using hstack) hperm
      (by rw [hcount]; omega) r2)

end Benchmarks.Morpho.MetaMorphoV1_1
