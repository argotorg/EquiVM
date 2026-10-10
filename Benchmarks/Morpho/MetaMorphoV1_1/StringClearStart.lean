import Benchmarks.Morpho.MetaMorphoV1_1.StringLongStore
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_017

/-! The clearing prefix computes the first obsolete word and the number of words to clear. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringClearStartPC (symbol : Bool) : UInt256 := if symbol then ⟨3345⟩ else ⟨2589⟩

def stringClearCountPC (symbol : Bool) : UInt256 := if symbol then ⟨3365⟩ else ⟨2609⟩

def stringFirstClearedWord (len : Nat) : Nat :=
  if len < 32 then 0 else solidityBytesDataWordCount len

theorem stringCeilWord (len : UInt256) (hbound : len.toNat < 2 ^ 255) :
    UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ =
      UInt256.ofNat (solidityBytesDataWordCount len.toNat) := by
  have ha : (len + (⟨31⟩ : UInt256)).toNat = len.toNat + 31 :=
    uadd_word_ofNat_toNat len 31 (by change _ < 2 ^ 256; omega)
  apply u256_inj
  change ((len + (⟨31⟩ : UInt256)).toNat >>> 5) % UInt256.size = _
  rw [ha, Nat.shiftRight_eq_div_pow]
  rfl

theorem stringClearChoose {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 5 ≤ 1024) (hsmall : len.toNat < 2 ^ 255)
    (rd : RD (deployedRuntime v) I g s0 (stringClearStartPC symbol)
      (old :: len :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringClearCountPC symbol)
      (old :: UInt256.ofNat (stringFirstClearedWord len.toNat) :: len :: R)
      (stringStorageScratch mem symbol) aw' out σ k' C' := by
  by_cases hs : len.toNat < 32
  · have hc : UInt256.lt len (UInt256.ofNat 32) ≠ UInt256.ofNat 0 := by
      rw [ult_one hs]; decide
    simp only [stringFirstClearedWord, if_pos hs]
    cases symbol with
    | false =>
        obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2589_taken_packed
          (immWords := wordsOf (immStore v)) hstack hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
        exact metaMorphoV1_1_block_2682_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    | true =>
        obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3345_taken_packed
          (immWords := wordsOf (immStore v)) hstack hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
        exact metaMorphoV1_1_block_3438_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  · have hc : UInt256.lt len (UInt256.ofNat 32) = UInt256.ofNat 0 :=
      ult_zero (by change 32 ≤ len.toNat; omega)
    simp only [stringFirstClearedWord, if_neg hs]
    rw [← stringCeilWord len hsmall]
    cases symbol with
    | false =>
        exact metaMorphoV1_1_block_2589_fallthrough_packed
          (immWords := wordsOf (immStore v)) hstack hc rd
    | true =>
        exact metaMorphoV1_1_block_3345_fallthrough_packed
          (immWords := wordsOf (immStore v)) hstack hc rd

theorem stringClearCount {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old first : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (stringClearCountPC symbol)
      (old :: first :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (⟨0⟩ :: first :: UInt256.sub (UInt256.shiftRight (old + ⟨31⟩) ⟨5⟩) first :: R)
      mem aw' out σ k' C' := by
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_2609_packed (immWords := wordsOf (immStore v)) hstack rd
  | true =>
      exact metaMorphoV1_1_block_3365_packed (immWords := wordsOf (immStore v)) hstack rd

theorem stringClearInit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 5 ≤ 1024) (hold : old.toNat < 2 ^ 255)
    (hsmall : len.toNat < 2 ^ 255) (hshrink : len.toNat ≤ old.toNat)
    (rd : RD (deployedRuntime v) I g s0 (stringClearStartPC symbol)
      (old :: len :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (⟨0⟩ :: UInt256.ofNat (stringFirstClearedWord len.toNat) ::
        UInt256.ofNat (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat) ::
        len :: R) (stringStorageScratch mem symbol) aw' out σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := stringClearChoose v symbol hstack hsmall rd
  obtain ⟨aw2, k2, C2, h2⟩ := stringClearCount v symbol
    (by simp only [List.length_cons]; omega) h1
  have hb : solidityBytesDataWordCount old.toNat < UInt256.size := by
    unfold solidityBytesDataWordCount
    change _ < 2 ^ 256
    omega
  have hs : stringFirstClearedWord len.toNat ≤ solidityBytesDataWordCount old.toNat := by
    unfold stringFirstClearedWord solidityBytesDataWordCount
    split <;> omega
  have he : UInt256.sub (UInt256.ofNat (solidityBytesDataWordCount old.toNat))
      (UInt256.ofNat (stringFirstClearedWord len.toNat)) =
      UInt256.ofNat (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat) := by
    apply u256_inj
    rw [usub_ofNat_lit_toNat hs hb, UInt256.toNat_ofNat_of_lt (by omega)]
  rw [stringCeilWord old hold, he] at h2
  exact ⟨aw2, k2, C2, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
