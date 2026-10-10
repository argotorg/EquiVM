import Benchmarks.Morpho.MetaMorphoV1_1.StringWriteRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.StringHeaderRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055

/-! The metadata setters validate the old header, update storage, emit, and return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringSetOwnerReturnPC (symbol : Bool) : UInt256 := if symbol then ⟨3024⟩ else ⟨2262⟩

theorem stringSetHeaderEntry {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 5 ≤ 1024) (hs : SourceState s0 I σ evm)
    (buffer : StringBuffer mem ptr.toNat bytes) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 (stringSetOwnerReturnPC symbol)
      (ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11801⟩
      (storageStringHeader evm (stringViewSlot symbol) :: stringOldLengthPC symbol ::
        UInt256.ofNat bytes.size :: ptr :: R) mem aw' out σ k' C' := by
  have hload : memLoad ptr mem = UInt256.ofNat bytes.size := by
    simpa only [u256_ofNat_toNat] using buffer.length
  have hc : UInt256.gt (memLoad ptr mem)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
      UInt256.ofNat 0 := by
    rw [hload]
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]
    change bytes.size ≤ 18446744073709551615
    norm_num only [Nat.reducePow] at hsmall
    omega
  have hh : storageStringHeader evm (stringViewSlot symbol) =
      solcSlotWord σ I (stringViewSlot symbol) := hs.storageRead _
  rw [hh, ← hload]
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2262_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hc rd
      exact metaMorphoV1_1_block_2279_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3024_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hc rd
      exact metaMorphoV1_1_block_3041_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem stringSetEventReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr dest free topic : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 11 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11086⟩
      (ptr :: dest :: ⟨2399⟩ :: free :: free :: topic :: R) mem aw out σ k C) :
    RDret (deployedRuntime v) g s0 σ ByteArray.empty := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_11086_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2399 (immWords := wordsOf (immStore v)) (by omega) hperm h1

theorem stringSetStorage {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr sel : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 12 ≤ 1024) (hs : SourceState s0 I σ evm)
    (buffer : StringBuffer mem ptr.toNat bytes) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 (stringSetOwnerReturnPC symbol)
      (ptr :: sel :: R) mem aw out σ k C) :
    (¬ storageStringValid (storageStringHeader evm (stringViewSlot symbol)) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (storageStringValid (storageStringHeader evm (stringViewSlot symbol)) ∧
      ((I.perm = false ∧ RDstatic (deployedRuntime v) g s0) ∨
        (I.perm = true ∧ RDret (deployedRuntime v) g s0
          (storageStringWriteState evm (stringViewSlot symbol) bytes).accountMap
          ByteArray.empty))) := by
  obtain ⟨aw1, k1, C1, h1⟩ := stringSetHeaderEntry v symbol
    (by simp only [List.length_cons]; omega) hs buffer hsmall rd
  by_cases hv : storageStringValid (storageStringHeader evm (stringViewSlot symbol))
  · obtain ⟨aw2, k2, C2, h2⟩ := storageStringDecoderReturn v
      (by simp only [List.length_cons]; omega) hv (by
        cases symbol <;> rw [metaMorphoV1_1PatchedValidJumps v] <;>
          unfold stringOldLengthPC <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> jump_dest) h1
    rcases stringStorageWrites v symbol hstack hs hv buffer hlo hfit hsmall h2 with
      hstatic | ⟨hp, before, aw3, k3, C3, _hb, _hf, h3⟩
    · exact .inr ⟨hv, .inl hstatic⟩
    · exact .inr ⟨hv, .inr ⟨hp, stringSetEventReturn v
        (by simp only [List.length_cons]; omega) hp h3⟩⟩
  · exact .inl ⟨hv, storageStringDecoderRevert v
      (by simp only [List.length_cons]; omega) hv h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
