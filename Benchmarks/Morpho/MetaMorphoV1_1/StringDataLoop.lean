import Benchmarks.Morpho.MetaMorphoV1_1.StringBufferWords
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_016
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_019

/-! The two metadata storage loops write the same full words as the Solidity storage backend. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringDataLoopPC (symbol : Bool) : UInt256 := if symbol then ⟨3217⟩ else ⟨2461⟩

def stringDataLoopExitPC (symbol : Bool) : UInt256 := if symbol then ⟨3225⟩ else ⟨2469⟩

theorem stringDataLoopExit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 4 ≤ 1024)
    (hcond : UInt256.lt off cutoff = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringDataLoopPC symbol)
      (off :: cutoff :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringDataLoopExitPC symbol)
      (off :: cutoff :: R) mem aw' out σ k' C' := by
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_2461_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hcond rd
  | true =>
      exact metaMorphoV1_1_block_3217_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hcond rd

theorem stringDataLoopStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff stride slot len ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 11 ≤ 1024)
    (hperm : I.perm = true) (hcond : UInt256.lt off cutoff ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringDataLoopPC symbol)
      (off :: cutoff :: stride :: slot :: len :: ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringDataLoopPC symbol)
      ((off + UInt256.ofNat 32) :: cutoff :: (stride + UInt256.ofNat 32) ::
        (slot + UInt256.ofNat 1) :: len :: ptr :: R) mem aw' out
      (sstoreAccountMap I.codeOwner σ slot (memLoad (ptr + stride) mem)) k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2461_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_2556_packed (immWords := wordsOf (immStore v)) hstack hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3217_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_3312_packed (immWords := wordsOf (immStore v)) hstack hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem stringDataWords {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {base cutoff len ptr : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (n i : Nat) (hstack : R.length + 11 ≤ 1024) (hperm : I.perm = true)
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hfull : (i + n) * 32 ≤ bytes.size) (hcut : cutoff.toNat = 32 * (i + n))
    (rd : RD (deployedRuntime v) I g s0 (stringDataLoopPC symbol)
      (UInt256.ofNat (32 * i) :: cutoff :: UInt256.ofNat (32 * (i + 1)) ::
        solidityBytesDataSlot base i :: len :: ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringDataLoopExitPC symbol)
      (UInt256.ofNat (32 * (i + n)) :: cutoff :: UInt256.ofNat (32 * (i + n + 1)) ::
        solidityBytesDataSlot base (i + n) :: len :: ptr :: R) mem aw' out
      (solidityDataWordsForwardFrom I.codeOwner σ base bytes i n) k' C' := by
  induction n generalizing i aw k C σ with
  | zero =>
      simpa only [Nat.add_zero, solidityDataWordsForwardFrom] using
        stringDataLoopExit v symbol (by simp only [List.length_cons]; omega)
          (ult_zero (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)) rd
  | succ n ih =>
      have hi : 32 * i + 32 ≤ bytes.size := by omega
      have hw : memLoad (ptr + UInt256.ofNat (32 * (i + 1))) mem =
          uInt256OfByteArray (bytes.readWithPadding (i * 32) 32) := by
        rw [show 32 * (i + 1) = 32 + 32 * i by omega, buffer.word hfit (32 * i) hi]
        rw [Nat.mul_comm i 32]
      obtain ⟨aw1, k1, C1, h1⟩ := stringDataLoopStep v symbol hstack hperm
        (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)]; decide) rd
      have hslot : solidityBytesDataSlot base i + UInt256.ofNat 1 =
          solidityBytesDataSlot base (i + 1) := by
        unfold solidityBytesDataSlot
        rw [u256_add_assoc, ofNat_add_words]
      simp only [hw, hslot, ofNat_add_words,
        show 32 * i + 32 = 32 * (i + 1) by omega,
        show 32 * (i + 1) + 32 = 32 * (i + 1 + 1) by omega] at h1
      obtain ⟨aw2, k2, C2, h2⟩ := ih (i + 1) (by omega) (by omega) h1
      exact ⟨aw2, k2, C2, by
        simpa only [solidityDataWordsForwardFrom,
          show i + 1 + n = i + (n + 1) by omega] using h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
