import Benchmarks.CompoundIII.Comet.WithdrawBaseRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyBaseRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free sender amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (dst : AccountAddress) (hstack : R.length + 15 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hmem : 96 ≤ mem.size)
    (hb : free.toNat + 160 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12473⟩
      (amount :: sender :: ⟨12591⟩ :: EVM.word dst.val :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      UserBasicMemory (withdrawBaseReadMemory mem free evm dst) free (withdrawBaseBasic evm dst) ∧
      RD (deployedRuntime v) ee g s0 ⟨12495⟩
        (free :: ⟨12604⟩ :: amount :: sender :: ⟨12591⟩ :: EVM.word dst.val :: ret :: R)
        (withdrawBaseReadMemory mem free evm dst) aw' rdata σ k' C'  := by
  have r1 := cometWithExtendedAssetList_block_12473
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 7 + 6 ≤ 1024; omega) (word_val_addr_canonical dst)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_12490
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hf : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (EVM.word dst.val) (UInt256.ofNat 5) mem) = free := by
    rw [twoWordHashMem_load_ge (mem := mem) (ptr := UInt256.ofNat 64)
      (EVM.word dst.val) (UInt256.ofNat 5) (by decide) hmem, hfree]
  obtain ⟨aw4, k4, C4, hm4, r4⟩ := cometAllocateUserBasic (v := v)
    (by change R.length + 6 + 9 ≤ 1024; omega) hf hb
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have hread : solcSlotWordAt (solcMappingSlot (UInt256.ofNat 5) (EVM.word dst.val)) σ ee =
      (withdrawBaseBasic evm dst).principal := by
    change solcSlotWordAt (userBasicSlot dst) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot dst)
    simpa only [hs.env] using (hs.storageRead (userBasicSlot dst)).symm
  rw [hread] at hm4 r4
  change UserBasicMemory (withdrawBaseReadMemory mem free evm dst) free
    (withdrawBaseBasic evm dst) at hm4
  exact ⟨_, _, _, hm4, r4⟩

end Benchmarks.CompoundIII.Comet
