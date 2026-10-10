import Benchmarks.Morpho.MetaMorphoV1_1.StringMask
import Benchmarks.Morpho.MetaMorphoV1_1.StringClearLoop
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_015
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! The short-string branches prepare the storage word and the metadata event arguments. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringSetTopic (symbol : Bool) : UInt256 :=
  if symbol then
    ⟨78680671315402528844431224777925815044696236461976684063792454754927954463430⟩
  else ⟨35269558340673015329533275355215762833668788681394645669427373890636468965122⟩

def stringShortSelectPC (symbol : Bool) : UInt256 := if symbol then ⟨3075⟩ else ⟨2313⟩

def stringShortStorePC (symbol : Bool) : UInt256 := if symbol then ⟨3121⟩ else ⟨2359⟩

theorem stringShortSelect {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk len : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 4 ≤ 1024) (hshort : len.toNat < 32)
    (rd : RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (junk :: len :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringShortSelectPC symbol)
      (⟨32⟩ :: len :: R) mem aw' out σ k' C' := by
  have hc : UInt256.eq (UInt256.ofNat 1) (UInt256.gt len (UInt256.ofNat 31)) =
      UInt256.ofNat 0 := by
    change UInt256.eq ⟨1⟩ (UInt256.lt ⟨31⟩ len) = ⟨0⟩
    rw [ult_zero (by change len.toNat ≤ 31; omega)]
    decide
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_2298_fallthrough_packed (immWords := wordsOf (immStore v))
        hstack hc rd
  | true =>
      exact metaMorphoV1_1_block_3060_fallthrough_packed (immWords := wordsOf (immStore v))
        hstack hc rd

theorem stringShortZero {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 8 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (stringShortSelectPC symbol)
      (⟨32⟩ :: ⟨0⟩ :: ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringShortStorePC symbol)
      (⟨32⟩ :: ⟨0⟩ :: ⟨0⟩ :: ptr :: ⟨2399⟩ :: stringSetTopic symbol :: R)
      mem aw' out σ k' C' := by
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_2313_fallthrough_packed (immWords := wordsOf (immStore v))
        hstack rfl rd
  | true =>
      exact metaMorphoV1_1_block_3075_fallthrough_packed (immWords := wordsOf (immStore v))
        hstack rfl rd

theorem stringShortNonzero {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {len ptr sel : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 9 ≤ 1024) (hnz : len ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringShortSelectPC symbol)
      (⟨32⟩ :: len :: ptr :: sel :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringShortStorePC symbol)
      (sel :: memLoad (ptr + ⟨32⟩) mem :: len :: ptr :: ⟨2399⟩ ::
        stringSetTopic symbol :: sel :: R) mem aw' out σ k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2313_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hnz
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_2404_packed (immWords := wordsOf (immStore v)) (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3075_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hnz
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_3160_packed (immWords := wordsOf (immStore v)) (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem stringShortReady {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk ptr sel : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 9 ≤ 1024)
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hshort : bytes.size < 32)
    (rd : RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (junk :: UInt256.ofNat bytes.size :: ptr :: sel :: R) mem aw out σ k C) :
    ∃ junk' word aw' k' C', stringPackedHeader word (UInt256.ofNat bytes.size) =
      solidityShortBytesWord bytes ∧
      RD (deployedRuntime v) I g s0 (stringShortStorePC symbol)
        (junk' :: word :: UInt256.ofNat bytes.size :: ptr :: ⟨2399⟩ ::
          stringSetTopic symbol :: sel :: R) mem aw' out σ k' C' := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by omega)
  obtain ⟨aw1, k1, C1, h1⟩ := stringShortSelect v symbol
    (by simp only [List.length_cons]; omega) (by omega) rd
  by_cases hz : bytes.size = 0
  · have he : bytes = ByteArray.empty := ByteArray.ext (Array.size_eq_zero_iff.mp hz)
    rw [hz] at h1
    obtain ⟨aw2, k2, C2, h2⟩ := stringShortZero v symbol
      (by simp only [List.length_cons]; omega) h1
    refine ⟨⟨32⟩, ⟨0⟩, aw2, k2, C2, ?_, ?_⟩
    · rw [he]; exact stringPackedHeader_empty
    · simpa only [hz] using h2
  · have hnz : UInt256.ofNat bytes.size ≠ (⟨0⟩ : UInt256) := by
      intro h
      have hnat := congrArg UInt256.toNat h
      rw [hn] at hnat
      exact hz hnat
    obtain ⟨aw2, k2, C2, h2⟩ := stringShortNonzero v symbol hstack hnz h1
    exact ⟨sel, _, aw2, k2, C2, buffer.packedHeader hfit hshort, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
