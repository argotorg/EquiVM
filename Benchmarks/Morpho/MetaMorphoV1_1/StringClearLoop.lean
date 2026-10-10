import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageHash
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_016
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_019
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_020

/-! Shared metadata loop clearing storage words beyond the new string. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringClearLoopPC (symbol : Bool) : UInt256 := if symbol then ⟨3377⟩ else ⟨2621⟩

def stringSetStoreSelectPC (symbol : Bool) : UInt256 := if symbol then ⟨3060⟩ else ⟨2298⟩

theorem stringClearLoopExit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i start count : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 5 ≤ 1024)
    (hcond : UInt256.lt i count = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (i :: start :: count :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (count :: R) mem aw' out σ k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2621_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hcond rd
      exact metaMorphoV1_1_block_2629_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3377_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hcond rd
      exact metaMorphoV1_1_block_3385_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem stringClearLoopStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i start count : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hcond : UInt256.lt i count ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (i :: start :: count :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      ((UInt256.ofNat 1 + i) :: start :: count :: R) mem aw' out
      (sstoreAccountMap I.codeOwner σ (stringStorageHash symbol + (i + start)) ⟨0⟩) k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2621_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_2635_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3377_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_3391_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem stringClearLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {start count : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (n i : Nat) (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hcount : count.toNat = i + n)
    (rd : RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (UInt256.ofNat i :: start :: count :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (count :: R) mem aw' out
      (clearDataWordsForwardFrom I.codeOwner σ (stringStorageHash symbol)
        (UInt256.ofNat i + start) n) k' C' := by
  have hb : count.toNat < UInt256.size := count.val.isLt
  induction n generalizing i σ aw k C with
  | zero =>
      exact stringClearLoopExit v symbol (by omega) (ult_zero (by
        rw [UInt256.toNat_ofNat_of_lt (by omega)]
        omega)) rd
  | succ n ih =>
      obtain ⟨aw1, k1, C1, h1⟩ := stringClearLoopStep v symbol hstack hperm
        (by rw [ult_one (by
              rw [UInt256.toNat_ofNat_of_lt (by omega)]
              omega)]
            decide) rd
      simp only [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, u256_one_add_ofNat] at h1
      obtain ⟨aw2, k2, C2, h2⟩ := ih (i + 1) (by omega) h1
      refine ⟨aw2, k2, C2, ?_⟩
      have hi : (⟨1⟩ : UInt256) + (UInt256.ofNat i + start) =
          UInt256.ofNat (i + 1) + start := by
        rw [← u256_add_assoc, u256_one_add_ofNat]
      simpa only [clearDataWordsForwardFrom, hi] using h2

theorem stringClearWords {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (symbol : Bool) (start count : Nat)
    (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = true) (hcount : count < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (⟨0⟩ :: UInt256.ofNat start :: UInt256.ofNat count :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (UInt256.ofNat count :: R) mem aw' out
      (clearDataWordsForwardFrom I.codeOwner σ (solidityBytesDataBaseSlot (stringViewSlot symbol))
        (UInt256.ofNat start) count) k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := stringClearLoop v symbol count 0 hstack hperm
    (by rw [UInt256.toNat_ofNat_of_lt hcount]; omega) rd
  exact ⟨aw1, k1, C1, by simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    u256_zero_add, stringStorageHash_eq] using h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
