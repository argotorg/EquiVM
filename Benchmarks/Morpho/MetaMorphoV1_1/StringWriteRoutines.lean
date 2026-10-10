import Benchmarks.Morpho.MetaMorphoV1_1.StringWriteState

/-! Complete storage-string writes after decoding a valid old header. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem stringStorageWrites {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr sel : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 12 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol)))
    (buffer : StringBuffer mem ptr.toNat bytes) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 (stringOldLengthPC symbol)
      (storageStringLength (storageStringHeader evm (stringViewSlot symbol)) ::
        UInt256.ofNat bytes.size :: ptr :: sel :: R) mem aw out σ k C) :
    (I.perm = false ∧ RDstatic (deployedRuntime v) g s0) ∨
    (I.perm = true ∧ ∃ before aw' k' C', StringBuffer before ptr.toNat bytes ∧
      memLoad ⟨64⟩ before = memLoad ⟨64⟩ mem ∧
      RD (deployedRuntime v) I g s0 ⟨11086⟩
        (ptr :: (memLoad ⟨64⟩ mem + ⟨32⟩) :: ⟨2399⟩ ::
          memLoad ⟨64⟩ mem :: memLoad ⟨64⟩ mem :: stringSetTopic symbol :: sel :: R)
        (stringEventMemory before) aw' out
        (storageStringWriteState evm (stringViewSlot symbol) bytes).accountMap k' C') := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by omega)
  rcases stringClearStorage v symbol (by simp only [List.length_cons]; omega)
    (storageStringLength_lt _) (by rw [hn]; omega) rd with
    hstatic | ⟨mem1, junk, aw1, k1, C1, hm, h1⟩
  · exact .inl hstatic
  · rw [hn] at h1
    have hb : StringBuffer mem1 ptr.toNat bytes := by
      rcases hm with rfl | rfl
      · exact buffer
      · exact buffer.storageScratch hlo symbol
    have hfree : memLoad ⟨64⟩ mem1 = memLoad ⟨64⟩ mem := by
      rcases hm with rfl | rfl
      · rfl
      · exact stringStorageScratch_free _ _ (by have hsz := buffer.size; omega)
    have ha := storageStringWriteState_accounts evm symbol bytes hvalid
    rw [hs.env, ← hs.accounts] at ha
    by_cases hshort : bytes.size < 32
    · rcases stringShortWrite v symbol (by omega) hb hfit hshort h1 with
        hstatic | ⟨hp, aw2, k2, C2, h2⟩
      · exact .inl hstatic
      · rw [if_pos hshort] at ha
        rw [hfree, ← ha] at h2
        exact .inr ⟨hp, mem1, aw2, k2, C2, hb, hfree, h2⟩
    · rcases stringLongWrite v symbol hstack hb hlo hfit (by omega) hsmall h1 with
        hstatic | ⟨hp, aw2, k2, C2, h2⟩
      · exact .inl hstatic
      · rw [if_neg hshort] at ha
        rw [hfree, ← ha] at h2
        exact .inr ⟨hp, stringStorageScratch mem1 symbol, aw2, k2, C2,
          hb.storageScratch hlo symbol,
          (stringStorageScratch_free _ _ (by have hsz := hb.size; omega)).trans hfree, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
