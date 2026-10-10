import Benchmarks.Morpho.MetaMorphoV1_1.StringLongTail

/-! Long metadata strings write all data words before the length header. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringStorageScratch (mem : ByteArray) (symbol : Bool) : ByteArray :=
  Reasoning.Theory.writeWord mem 0 (stringViewSlot symbol)

theorem StringBuffer.storageScratch {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : StringBuffer mem ptr.toNat bytes) (hlo : 96 ≤ ptr.toNat) (symbol : Bool) :
    StringBuffer (stringStorageScratch mem symbol) ptr.toNat bytes := by
  exact buffer.preserve
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide))) hlo ptr.val.isLt (le_refl _)

theorem stringStorageScratch_free (mem : ByteArray) (symbol : Bool) (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (stringStorageScratch mem symbol) = memLoad ⟨64⟩ mem := by
  unfold stringStorageScratch Reasoning.Theory.writeWord
  exact memLoad_write_disjoint _ _ _ _ hmem (.inr (by decide))

theorem stringLongStart {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk len : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 5 ≤ 1024) (hlong : 32 ≤ len.toNat)
    (rd : RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (junk :: len :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringDataLoopPC symbol)
      (⟨0⟩ :: UInt256.land len (UInt256.lnot ⟨31⟩) :: ⟨32⟩ ::
        solidityBytesDataSlot (stringViewSlot symbol) 0 :: len :: R)
      (stringStorageScratch mem symbol) aw' out σ k' C' := by
  have hc : UInt256.eq (UInt256.ofNat 1) (UInt256.gt len (UInt256.ofNat 31)) ≠
      UInt256.ofNat 0 := by
    change UInt256.eq ⟨1⟩ (UInt256.lt ⟨31⟩ len) ≠ ⟨0⟩
    rw [ult_one (by change 31 < len.toNat; omega)]
    decide
  have hs : solidityBytesDataSlot (stringViewSlot symbol) 0 = stringStorageHash symbol := by
    rw [solidityBytesDataSlot, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero, stringStorageHash_eq]
  rw [hs]
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2298_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_2415_packed (immWords := wordsOf (immStore v)) hstack h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3060_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_3171_packed (immWords := wordsOf (immStore v)) hstack h1

theorem stringDataLoopStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff stride slot len ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 11 ≤ 1024)
    (hperm : I.perm = false) (hcond : UInt256.lt off cutoff ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringDataLoopPC symbol)
      (off :: cutoff :: stride :: slot :: len :: ptr :: R) mem aw out σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2461_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact stringDataBodyStatic v false hstack hperm h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3217_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact stringDataBodyStatic v true hstack hperm h1

theorem stringLongWrite {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk ptr sel : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 12 ≤ 1024)
    (buffer : StringBuffer mem ptr.toNat bytes) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hlong : 32 ≤ bytes.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (junk :: UInt256.ofNat bytes.size :: ptr :: sel :: R) mem aw out σ k C) :
    (I.perm = false ∧ RDstatic (deployedRuntime v) g s0) ∨
    (I.perm = true ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11086⟩
      (ptr :: (memLoad ⟨64⟩ mem + ⟨32⟩) :: ⟨2399⟩ ::
        memLoad ⟨64⟩ mem :: memLoad ⟨64⟩ mem :: stringSetTopic symbol :: sel :: R)
      (stringEventMemory (stringStorageScratch mem symbol)) aw' out
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner σ (stringViewSlot symbol) bytes 0
          (solidityBytesDataWordCount bytes.size))
        (stringViewSlot symbol) (solidityBytesHeaderWord bytes.size)) k' C') := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by omega)
  obtain ⟨aw1, k1, C1, h1⟩ := stringLongStart v symbol
    (by simp only [List.length_cons]; omega) (by omega) rd
  have hb := buffer.storageScratch hlo symbol
  cases hp : I.perm with
  | false =>
      refine .inl ⟨rfl, stringDataLoopStatic v symbol
        (by simp only [List.length_cons]; omega) hp ?_ h1⟩
      rw [ult_one (by rw [longDataCutoff_toNat, hn]; change 0 < _; omega)]
      decide
  | true =>
      obtain ⟨aw2, k2, C2, h2⟩ := stringDataWords v symbol (bytes.size / 32) 0
        (by simp only [List.length_cons]; omega) hp hb hfit (by omega)
        (by rw [longDataCutoff_toNat, hn]; omega) h1
      simp only [Nat.zero_add] at h2
      obtain ⟨aw3, k3, C3, h3⟩ := stringDataFinish v symbol hstack hp hb hfit hlong hsmall h2
      obtain ⟨aw4, k4, C4, h4⟩ := stringEventPrepare v
        (by simp only [List.length_cons]; omega) h3
      rw [stringStorageScratch_free mem symbol (by have hs := buffer.size; omega)] at h4
      exact .inr ⟨rfl, aw4, k4, C4, h4⟩

end Benchmarks.Morpho.MetaMorphoV1_1
