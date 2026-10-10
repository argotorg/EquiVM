import Benchmarks.Morpho.MetaMorphoV1_1.StringStoreStatic

/-! Packed metadata writes, including the static-call branch and event encoder setup. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringEventMemory (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem (memLoad ⟨64⟩ mem).toNat ⟨32⟩

theorem stringEventPrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 6 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨2379⟩ (ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11086⟩
      (ptr :: (memLoad ⟨64⟩ mem + ⟨32⟩) :: ret ::
        memLoad ⟨64⟩ mem :: memLoad ⟨64⟩ mem :: R)
      (stringEventMemory mem) aw' out σ k' C' := by
  exact metaMorphoV1_1_block_2379_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem stringShortStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk word len ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 (stringShortStorePC symbol)
      (junk :: word :: len :: ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11086⟩
      (ptr :: (memLoad ⟨64⟩ mem + ⟨32⟩) :: ret ::
        memLoad ⟨64⟩ mem :: memLoad ⟨64⟩ mem :: R)
      (stringEventMemory mem) aw' out
      (sstoreAccountMap I.codeOwner σ (stringViewSlot symbol) (stringPackedHeader word len))
      k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2359_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hperm rd
      exact stringEventPrepare v (by omega) h1
  | true =>
      exact metaMorphoV1_1_block_3121_packed (immWords := wordsOf (immStore v)) hstack hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem stringShortWrite {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk ptr sel : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 9 ≤ 1024)
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hshort : bytes.size < 32)
    (rd : RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (junk :: UInt256.ofNat bytes.size :: ptr :: sel :: R) mem aw out σ k C) :
    (I.perm = false ∧ RDstatic (deployedRuntime v) g s0) ∨
    (I.perm = true ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11086⟩
      (ptr :: (memLoad ⟨64⟩ mem + ⟨32⟩) :: ⟨2399⟩ ::
        memLoad ⟨64⟩ mem :: memLoad ⟨64⟩ mem :: stringSetTopic symbol :: sel :: R)
      (stringEventMemory mem) aw' out
      (sstoreAccountMap I.codeOwner σ (stringViewSlot symbol) (solidityShortBytesWord bytes))
      k' C') := by
  obtain ⟨junk1, word, aw1, k1, C1, hw, h1⟩ :=
    stringShortReady v symbol hstack buffer hfit hshort rd
  cases hp : I.perm with
  | false =>
      exact .inl ⟨rfl, stringShortStoreStatic v symbol
        (by simp only [List.length_cons]; omega) hp h1⟩
  | true =>
      obtain ⟨aw2, k2, C2, h2⟩ := stringShortStore v symbol
        (by simp only [List.length_cons]; omega) hp h1
      rw [hw] at h2
      exact .inr ⟨rfl, aw2, k2, C2, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
