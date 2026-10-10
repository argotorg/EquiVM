import Benchmarks.CompoundIII.Comet.WordStructStore
import Benchmarks.CompoundIII.Comet.UserBasicMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_029

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def userBasicMemoryOf (mem : ByteArray) (ptr word : UInt256) : ByteArray :=
  wordStructStore mem ptr 5 (userBasicMemWord (userBasicData word))

theorem userBasicMemoryOf_correct (mem : ByteArray) (ptr word : UInt256)
    (hb : ptr.toNat + 160 < UInt256.size) :
    UserBasicMemory (userBasicMemoryOf mem ptr word) ptr (userBasicData word) :=
  wordStructStore_memory (by decide) hb

theorem userBasicLoad_memory (ee : ExecutionEnv) (σ : AccountMap)
    (mem : ByteArray) (ptr slot : UInt256) :
    cometWithExtendedAssetList_block_5353_memory
      (ee := ee) (σ := σ) (mem := mem) (x0 := slot) (x2 := ptr) =
      userBasicMemoryOf mem ptr (solcSlotWordAt slot σ ee) := by
  simp only [userBasicMemoryOf, wordStructStore_succ, wordStructStore_zero,
    userBasicMemWord, userBasicData]
  rw [(userBasicFieldWords _).1, (userBasicFieldWords _).2.1,
    (userBasicFieldWords _).2.2.1, (userBasicFieldWords _).2.2.2]
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right]
  unfold cometWithExtendedAssetList_block_5353_memory
  rw [u256_land_comm (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
    (UInt256.ofNat 64)) (UInt256.ofNat 1))]
  rfl

theorem cometLoadUserBasic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr slot ret : UInt256}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hptr : ptr.toNat + 160 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨5353⟩ (slot :: ret :: ptr :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C',
      UserBasicMemory (userBasicMemoryOf mem ptr (solcSlotWordAt slot σ ee)) ptr
        (userBasicData (solcSlotWordAt slot σ ee)) ∧
      RD (deployedRuntime v) ee g s0 ret (ptr :: R)
        (userBasicMemoryOf mem ptr (solcSlotWordAt slot σ ee)) aw' rdata σ k' C' := by
  obtain ⟨k', C', hr⟩ := cometWithExtendedAssetList_block_5353
    (immWords := wordsOf (immStore v)) hstack hret h
  rw [userBasicLoad_memory] at hr
  exact ⟨_, k', C', userBasicMemoryOf_correct mem ptr _ hptr, hr⟩

end Benchmarks.CompoundIII.Comet
