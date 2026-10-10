import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeEntry
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_038
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010

/-! Fee equality, maximum-fee, and recipient checks before interest accrual. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def setFeeInvalidWord (old value : UInt256) : UInt256 :=
  if value = ⟨0⟩ then ⟨0⟩ else UInt256.isZero (UInt256.shiftRight old ⟨96⟩)

theorem setFeeInvalidWord_zero (old value : UInt256)
    (hvalid : ¬ (value ≠ ⟨0⟩ ∧ UInt256.shiftRight old ⟨96⟩ = ⟨0⟩)) :
    setFeeInvalidWord old value = ⟨0⟩ := by
  by_cases hz : value = ⟨0⟩
  · simp only [setFeeInvalidWord, if_pos hz]
  · rw [setFeeInvalidWord, if_neg hz]
    exact isZero_eq_zero_of_ne (fun heq ↦ hvalid ⟨hz, heq⟩)

theorem setFeeDifferentGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hne : w ≠ UInt256.land (codeOwnerStorageWord I σ ⟨18⟩) (UInt256.ofNat (2 ^ 96 - 1)))
    (rd : RD (deployedRuntime v) I g s0 ⟨7445⟩ (w :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨7465⟩
      (codeOwnerStorageWord I σ ⟨18⟩ :: w :: R) mem aw' rdata σ k' C' := by
  exact metaMorphoV1_1_block_7445_fallthrough_packed (immWords := wordsOf (immStore v))
    hstack (u256_eq_of_ne hne) rd

theorem setFeeSameRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (heq : w = UInt256.land (codeOwnerStorageWord I σ ⟨18⟩) (UInt256.ofNat (2 ^ 96 - 1)))
    (rd : RD (deployedRuntime v) I g s0 ⟨7445⟩ (w :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.eq w
      (UInt256.land (codeOwnerStorageWord I σ ⟨18⟩) (UInt256.ofNat (2 ^ 96 - 1))) ≠ ⟨0⟩ := by
    rw [heq, u256_eq_refl]; decide
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7445_taken_packed
    (immWords := wordsOf (immStore v)) hstack hc
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_1143 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_7445_taken_stack, List.length_cons]; omega) h1

theorem setFeeBoundGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hbound : w.toNat ≤ 500000000000000000)
    (rd : RD (deployedRuntime v) I g s0 ⟨7465⟩ (old :: w :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨7480⟩
      (old :: w :: R) mem aw' rdata σ k' C' := by
  exact metaMorphoV1_1_block_7465_fallthrough_packed (immWords := wordsOf (immStore v))
    hstack (ugt_zero (show w.toNat ≤ (UInt256.ofNat 500000000000000000).toNat from hbound)) rd

theorem setFeeBoundRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hbound : ¬ w.toNat ≤ 500000000000000000)
    (rd : RD (deployedRuntime v) I g s0 ⟨7465⟩ (old :: w :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.gt w (UInt256.ofNat 500000000000000000) ≠ ⟨0⟩ := by
    rw [ugt_one (show (UInt256.ofNat 500000000000000000).toNat < w.toNat from
      Nat.lt_of_not_ge hbound)]
    decide
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7465_taken_packed
    (immWords := wordsOf (immStore v)) hstack hc
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_7588 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) h1

theorem setFeeReachValidity {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨7480⟩ (old :: w :: tag :: R) mem aw rdata σ k C) :
    ∃ junk aw' k' C', RD (deployedRuntime v) I g s0 ⟨7489⟩
      (junk :: setFeeInvalidWord old w :: w :: tag :: R) mem aw' rdata σ k' C' := by
  by_cases hz : w = ⟨0⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7480_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hz]; rfl) rd
    refine ⟨old, aw1, k1, C1, ?_⟩
    simpa only [metaMorphoV1_1_block_7480_fallthrough_stack, setFeeInvalidWord, if_pos hz,
      hz, show UInt256.isZero (UInt256.isZero ⟨0⟩) = ⟨0⟩ from rfl] using h1
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7480_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [isZero_eq_zero_of_ne hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_7576_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    refine ⟨tag, aw2, k2, C2, ?_⟩
    simpa only [setFeeInvalidWord, if_neg hz] using h2

theorem setFeeReachAccrual {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hvalid : ¬ (w ≠ ⟨0⟩ ∧ UInt256.shiftRight old ⟨96⟩ = ⟨0⟩))
    (rd : RD (deployedRuntime v) I g s0 ⟨7480⟩ (old :: w :: tag :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14262⟩
      (⟨7511⟩ :: w :: UInt256.ofNat (2 ^ 96 - 1) :: tag :: R) mem aw' rdata σ k' C' := by
  obtain ⟨junk, aw1, k1, C1, h1⟩ := setFeeReachValidity v hstack rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_7489_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (setFeeInvalidWord_zero old w hvalid) h1
  exact metaMorphoV1_1_block_7495_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem setFeeInvalidRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hbad : w ≠ ⟨0⟩ ∧ UInt256.shiftRight old ⟨96⟩ = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7480⟩ (old :: w :: tag :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨junk, aw1, k1, C1, h1⟩ := setFeeReachValidity v hstack rd
  have hc : setFeeInvalidWord old w ≠ ⟨0⟩ := by
    rw [setFeeInvalidWord, if_neg hbad.1, hbad.2]; decide
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_7489_taken_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hc
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_1302 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_7489_taken_stack, List.length_cons]; omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
