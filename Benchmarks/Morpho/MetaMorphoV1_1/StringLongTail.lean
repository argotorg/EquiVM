import Benchmarks.Morpho.MetaMorphoV1_1.StringDataLoop
import Benchmarks.Morpho.MetaMorphoV1_1.StringShortStore

/-! Final data-word and length-header writes for long metadata strings. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringLongHeader (len : UInt256) : UInt256 := UInt256.shiftLeft len ⟨1⟩ + ⟨1⟩

theorem stringLongHeader_eq (size : Nat) (hlong : 32 ≤ size) :
    stringLongHeader (UInt256.ofNat size) = solidityBytesHeaderWord size := by
  unfold stringLongHeader solidityBytesHeaderWord
  rw [if_neg (by omega)]
  apply u256_inj
  change ((((size % UInt256.size) <<< 1) % UInt256.size) + 1) % UInt256.size =
    (size * 2 + 1) % UInt256.size
  rw [Nat.shiftLeft_eq]
  norm_num only [Nat.pow_one]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem stringLongNoTail {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff stride slot len ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 9 ≤ 1024)
    (hperm : I.perm = true) (hcond : UInt256.lt cutoff len = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringDataLoopExitPC symbol)
      (off :: cutoff :: stride :: slot :: len :: ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨2379⟩
      (ptr :: ⟨2399⟩ :: stringSetTopic symbol :: R) mem aw' out
      (sstoreAccountMap I.codeOwner σ (stringViewSlot symbol) (stringLongHeader len)) k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2469_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hcond rd
      exact metaMorphoV1_1_block_2519_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3225_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hcond rd
      exact metaMorphoV1_1_block_3275_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem stringLongTail {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff stride slot len ptr sel : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 12 ≤ 1024)
    (hperm : I.perm = true) (hcond : UInt256.lt cutoff len ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringDataLoopExitPC symbol)
      (off :: cutoff :: stride :: slot :: len :: ptr :: sel :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨2379⟩
      (ptr :: ⟨2399⟩ :: stringSetTopic symbol :: sel :: R) mem aw' out
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ slot
          (stringStorageTailWord (memLoad (ptr + stride) mem) len))
        (stringViewSlot symbol) (stringLongHeader len)) k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2469_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_2532_packed
        (immWords := wordsOf (immStore v)) hstack hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact metaMorphoV1_1_block_2519_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3225_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_3288_packed
        (immWords := wordsOf (immStore v)) hstack hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact metaMorphoV1_1_block_3275_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem stringDataFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr sel : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 12 ≤ 1024)
    (hperm : I.perm = true) (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hlong : 32 ≤ bytes.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 (stringDataLoopExitPC symbol)
      (UInt256.ofNat (32 * (bytes.size / 32)) ::
        UInt256.land (UInt256.ofNat bytes.size) (UInt256.lnot ⟨31⟩) ::
        UInt256.ofNat (32 * (bytes.size / 32 + 1)) ::
        solidityBytesDataSlot (stringViewSlot symbol) (bytes.size / 32) ::
        UInt256.ofNat bytes.size :: ptr :: sel :: R) mem aw out
      (solidityDataWordsForwardFrom I.codeOwner σ (stringViewSlot symbol) bytes 0
        (bytes.size / 32)) k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨2379⟩
      (ptr :: ⟨2399⟩ :: stringSetTopic symbol :: sel :: R) mem aw' out
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner σ (stringViewSlot symbol) bytes 0
          (solidityBytesDataWordCount bytes.size))
        (stringViewSlot symbol) (solidityBytesHeaderWord bytes.size)) k' C' := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by omega)
  by_cases hz : bytes.size % 32 = 0
  · obtain ⟨aw1, k1, C1, h1⟩ := stringLongNoTail v symbol
      (by simp only [List.length_cons]; omega) hperm (longDataNoTail _ (by rw [hn]; exact hz)) rd
    have hc : solidityBytesDataWordCount bytes.size = bytes.size / 32 := by
      unfold solidityBytesDataWordCount
      omega
    rw [stringLongHeader_eq _ hlong] at h1
    exact ⟨aw1, k1, C1, by simpa only [hc] using h1⟩
  · have hcond : UInt256.lt (UInt256.land (UInt256.ofNat bytes.size) (UInt256.lnot ⟨31⟩))
        (UInt256.ofNat bytes.size) ≠ (⟨0⟩ : UInt256) := by
      rw [ult_one (by rw [longDataCutoff_toNat, hn]; omega)]
      decide
    obtain ⟨aw1, k1, C1, h1⟩ := stringLongTail v symbol hstack hperm hcond rd
    change RD _ _ _ _ _ _ _ _ _
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner _ _ (stringStorageTailWord _ _)) _ (stringLongHeader _))
      _ _ at h1
    rw [buffer.storageTail hfit hn hsmall hz, stringLongHeader_eq _ hlong] at h1
    have hc : solidityBytesDataWordCount bytes.size = bytes.size / 32 + 1 := by
      unfold solidityBytesDataWordCount
      omega
    refine ⟨aw1, k1, C1, ?_⟩
    rw [hc, solidityDataWordsForwardFrom_append]
    simpa only [solidityDataWordsForwardFrom, Nat.zero_add] using h1

end Benchmarks.Morpho.MetaMorphoV1_1
