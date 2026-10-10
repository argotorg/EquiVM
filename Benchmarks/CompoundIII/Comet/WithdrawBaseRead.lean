import Benchmarks.CompoundIII.Comet.UserBasicAllocation
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_057
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_072
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawBaseBasic (evm : EVM.State) (src : AccountAddress) : UserBasicData :=
  userBasicData (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot src))

def withdrawBaseReadMemory (mem : ByteArray) (free : UInt256) (evm : EVM.State)
    (src : AccountAddress) : ByteArray :=
  userBasicAllocatedMemory (twoWordHashMem (EVM.word src.val) ⟨5⟩ mem) free
    (withdrawBaseBasic evm src).principal

theorem withdrawBaseReadMemory_free (mem : ByteArray) (free : UInt256) (evm : EVM.State)
    (src : AccountAddress) (hlo : 96 ≤ free.toNat) (hb : free.toNat + 160 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (withdrawBaseReadMemory mem free evm src) = free + ⟨160⟩ :=
  userBasicAllocatedMemory_free _ _ _ hlo hb

theorem cometWithdrawBaseRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free recipient amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src : AccountAddress) (hstack : R.length + 13 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hmem : 96 ≤ mem.size)
    (hb : free.toNat + 160 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15748⟩
      (recipient :: amount :: EVM.word src.val :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      UserBasicMemory (withdrawBaseReadMemory mem free evm src) free (withdrawBaseBasic evm src) ∧
      RD (deployedRuntime v) ee g s0 ⟨15776⟩
        (UInt256.signextend (UInt256.ofNat 12) (withdrawBaseBasic evm src).principal ::
          UInt256.ofNat 15852 :: free :: recipient :: amount :: EVM.word src.val :: ret :: R)
        (withdrawBaseReadMemory mem free evm src) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_15748
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 5 + 6 ≤ 1024; omega) (word_val_addr_canonical src)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_12490
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hf : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (EVM.word src.val) (UInt256.ofNat 5) mem) = free := by
    rw [twoWordHashMem_load_ge (mem := mem) (ptr := UInt256.ofNat 64)
      (EVM.word src.val) (UInt256.ofNat 5) (by decide) hmem, hfree]
  obtain ⟨aw4, k4, C4, hm4, r4⟩ := cometAllocateUserBasic (v := v)
    (by change R.length + 4 + 9 ≤ 1024; omega) hf hb
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have hread : solcSlotWordAt (solcMappingSlot (UInt256.ofNat 5) (EVM.word src.val)) σ ee =
      (withdrawBaseBasic evm src).principal := by
    change solcSlotWordAt (userBasicSlot src) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot src)
    simpa only [hs.env] using (hs.storageRead (userBasicSlot src)).symm
  rw [hread] at hm4 r4
  change UserBasicMemory (withdrawBaseReadMemory mem free evm src) free
    (withdrawBaseBasic evm src) at hm4
  have hpr : memLoad free (withdrawBaseReadMemory mem free evm src) =
      UInt256.signextend (UInt256.ofNat 12) (withdrawBaseBasic evm src).principal := hm4.principal
  have r5 := cometWithExtendedAssetList_block_15762
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  change RD _ _ _ _ _ (UInt256.signextend (UInt256.ofNat 12)
    (memLoad free (withdrawBaseReadMemory mem free evm src)) :: UInt256.ofNat 15852 :: free ::
    recipient :: amount :: EVM.word src.val :: ret :: R) _ _ _ _ _ _ at r5
  rw [hpr, signextend104_idem] at r5
  exact ⟨_, _, _, hm4, r5⟩

end Benchmarks.CompoundIII.Comet
