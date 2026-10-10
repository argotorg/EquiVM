import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueStorage
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayPrefix
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_041
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_042

/-! Copy the completed replacement array from memory into withdrawal-queue storage. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueWriteLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i ptr : Nat}
    {queue : List UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 7 ≤ 1024)
    (hm : WordArrayPrefix mem ptr queue queue.length) (hperm : I.perm = true)
    (hdiff : queue.length = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨8235⟩
      ([UInt256.ofNat i, UInt256.ofNat (ptr + 32 + 32 * i), UInt256.ofNat queue.length] ++ R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8243⟩
      ([UInt256.ofNat queue.length, UInt256.ofNat (ptr + 32 + 32 * queue.length),
        UInt256.ofNat queue.length] ++ R) mem aw' out
      (storeWordArray I.codeOwner σ (solidityBytesDataBaseSlot ⟨21⟩)
        (fun j ↦ queue[j]?.getD ⟨0⟩) i remaining) k' C' := by
  have hlen : queue.length < UInt256.size := by have := hm.fit; omega
  induction remaining generalizing i σ aw k C with
  | zero =>
      have hi : i = queue.length := by omega
      subst i
      have r1 := metaMorphoV1_1_block_8235_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 5 ≤ 1024; omega) (ult_zero (le_refl _)) rd
      exact ⟨_, _, _, r1⟩
  | succ n ih =>
      have hi : i < queue.length := by omega
      have hword : (UInt256.ofNat i).toNat < (UInt256.ofNat queue.length).toNat := by
        rw [ulit_toNat' i (by omega), ulit_toNat' _ hlen]; exact hi
      have hload : memLoad (UInt256.ofNat (ptr + 32 + 32 * i)) mem = queue[i]?.getD ⟨0⟩ := by
        rw [List.getElem?_eq_getElem hi, Option.getD_some]
        exact hm.data i hi
      have r1 := metaMorphoV1_1_block_8235_taken (immWords := wordsOf (immStore v))
        (by change R.length + 5 ≤ 1024; omega) (by rw [ult_one hword]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨k2, C2, r2⟩ := metaMorphoV1_1_block_8340 (immWords := wordsOf (immStore v))
        (by change (_ :: R).length + 6 ≤ 1024; simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
      have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
        (u256_add_comm _ _).trans (u256_one_add_ofNat i)
      have hstep : UInt256.ofNat (ptr + 32 + 32 * i) + UInt256.ofNat 32 =
          UInt256.ofNat (ptr + 32 + 32 * (i + 1)) := by
        apply (u256_add_comm _ _).trans
        exact (u256_32_add_ofNat _).trans (congrArg UInt256.ofNat (by omega))
      simp only [metaMorphoV1_1_block_8340_stack, hadd, hstep, hload,
        ← withdrawQueueDataBase_eq] at r2
      exact ih (by omega) r2

end Benchmarks.Morpho.MetaMorphoV1_1
