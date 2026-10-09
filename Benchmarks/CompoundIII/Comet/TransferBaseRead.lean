import Benchmarks.CompoundIII.Comet.WithdrawBaseRead
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_068

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferBaseReadMemory (mem : ByteArray) (free : UInt256) (evm : EVM.State)
    (src dst : AccountAddress) : ByteArray :=
  withdrawBaseReadMemory (withdrawBaseReadMemory mem free evm src) (free + ⟨160⟩) evm dst

theorem transferBaseReadMemory_free (mem : ByteArray) (free : UInt256) (evm : EVM.State)
    (src dst : AccountAddress) (hlo : 96 ≤ free.toNat)
    (hb : free.toNat + 320 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (transferBaseReadMemory mem free evm src dst) = free + ⟨320⟩ := by
  have ha : (free + ⟨160⟩).toNat = free.toNat + 160 :=
    uadd_word_ofNat_toNat free 160 (by omega)
  rw [transferBaseReadMemory, withdrawBaseReadMemory_free _ _ _ _ (by omega) (by omega),
    u256_add_assoc]
  rfl

theorem transferBaseReadMemory_preserve {mem free evm src dst}
    (h : UserBasicMemory (withdrawBaseReadMemory mem free evm src) free
      (withdrawBaseBasic evm src)) (hlo : 96 ≤ free.toNat)
    (hb : free.toNat + 320 < UInt256.size) :
    UserBasicMemory (transferBaseReadMemory mem free evm src dst) free
      (withdrawBaseBasic evm src) := by
  have ha : (free + ⟨160⟩).toNat = free.toNat + 160 :=
    uadd_word_ofNat_toNat free 160 (by omega)
  apply (h.scratch hlo (EVM.word dst.val) (UInt256.ofNat 5)).preserve hlo
  have hp := userBasicAllocatedMemory_prefix
    (twoWordHashMem (EVM.word dst.val) (UInt256.ofNat 5)
      (withdrawBaseReadMemory mem free evm src)) (free + ⟨160⟩)
    (withdrawBaseBasic evm dst).principal (by omega)
  change MemoryPrefix _ (transferBaseReadMemory mem free evm src dst) _ at hp
  exact hp.mono (by change _ + 160 ≤ _; omega)

theorem cometTransferBaseRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst : AccountAddress) (hstack : R.length + 14 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hlo : 96 ≤ free.toNat)
    (hmem : 96 ≤ mem.size) (hb : free.toNat + 320 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14675⟩
      (EVM.word src.val :: amount :: EVM.word dst.val :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      UserBasicMemory (transferBaseReadMemory mem free evm src dst) free
        (withdrawBaseBasic evm src) ∧
      UserBasicMemory (transferBaseReadMemory mem free evm src dst) (free + ⟨160⟩)
        (withdrawBaseBasic evm dst) ∧
      RD (deployedRuntime v) ee g s0 ⟨14741⟩
        (UInt256.signextend (UInt256.ofNat 12) (withdrawBaseBasic evm dst).principal ::
          (free + ⟨160⟩) :: amount :: free :: EVM.word src.val ::
          UInt256.signextend (UInt256.ofNat 12) (withdrawBaseBasic evm src).principal ::
          EVM.word dst.val :: ret :: R)
        (transferBaseReadMemory mem free evm src dst) aw' rdata σ k' C' := by
  have ha : (free + ⟨160⟩).toNat = free.toNat + 160 :=
    uadd_word_ofNat_toNat free 160 (by change _ < 2^256; omega)
  have r1 := cometWithExtendedAssetList_block_14675
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 4 + 6 ≤ 1024; omega) (word_val_addr_canonical src)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_14686
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hf1 : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (EVM.word src.val) (UInt256.ofNat 5) mem) = free := by
    rw [twoWordHashMem_load_ge (mem := mem) (ptr := UInt256.ofNat 64)
      (EVM.word src.val) (UInt256.ofNat 5) (by decide) hmem, hfree]
  obtain ⟨aw4, k4, C4, hm4, r4⟩ := cometAllocateUserBasic (v := v)
    (by change R.length + 4 + 9 ≤ 1024; omega) hf1 (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have hread (a : AccountAddress) :
      solcSlotWordAt (solcMappingSlot (UInt256.ofNat 5) (EVM.word a.val)) σ ee =
        (withdrawBaseBasic evm a).principal := by
    change solcSlotWordAt (userBasicSlot a) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot a)
    simpa only [hs.env] using (hs.storageRead (userBasicSlot a)).symm
  rw [hread src] at hm4 r4
  change UserBasicMemory (withdrawBaseReadMemory mem free evm src) free
    (withdrawBaseBasic evm src) at hm4
  have r5 := cometWithExtendedAssetList_block_14695
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  obtain ⟨aw6, k6, C6, r6⟩ := cometMappingHash (v := v)
    (by change R.length + 5 + 6 ≤ 1024; omega) (word_val_addr_canonical dst)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
  have r7 := cometWithExtendedAssetList_block_14706
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
  have hsz : 96 ≤ (withdrawBaseReadMemory mem free evm src).size := by
    have hsize := hm4.size
    change free.toNat + 160 ≤ _ at hsize
    omega
  have hf2 : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (EVM.word dst.val) (UInt256.ofNat 5)
        (withdrawBaseReadMemory mem free evm src)) = free + ⟨160⟩ := by
    rw [twoWordHashMem_load_ge (ptr := UInt256.ofNat 64) _ _ (by decide) hsz,
      withdrawBaseReadMemory_free _ _ _ _ hlo (by change _ < 2^256; omega)]
  obtain ⟨aw8, k8, C8, hm8, r8⟩ := cometAllocateUserBasic (v := v)
    (by change R.length + 5 + 9 ≤ 1024; omega) hf2 (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
  rw [hread dst] at hm8 r8
  change UserBasicMemory (transferBaseReadMemory mem free evm src dst) (free + ⟨160⟩)
    (withdrawBaseBasic evm dst) at hm8
  have hsrc : UserBasicMemory (transferBaseReadMemory mem free evm src dst) free
      (withdrawBaseBasic evm src) :=
    transferBaseReadMemory_preserve hm4 hlo (by change _ < 2^256; omega)
  have r9 := cometWithExtendedAssetList_block_14715
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
  change RD _ _ _ _ _ (UInt256.signextend (UInt256.ofNat 12)
    (memLoad free (transferBaseReadMemory mem free evm src dst)) :: amount :: free ::
    EVM.word src.val :: (free + ⟨160⟩) :: EVM.word dst.val :: ret :: R) _ _ _ _ _ _ at r9
  have hsp : memLoad free (transferBaseReadMemory mem free evm src dst) =
      UInt256.signextend (UInt256.ofNat 12) (withdrawBaseBasic evm src).principal := hsrc.principal
  rw [hsp, signextend104_idem] at r9
  have r10 := cometWithExtendedAssetList_block_14728
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r9
  change RD _ _ _ _ _ (UInt256.signextend (UInt256.ofNat 12)
    (memLoad (free + ⟨160⟩) (transferBaseReadMemory mem free evm src dst)) ::
    (free + ⟨160⟩) :: amount :: free :: EVM.word src.val ::
    UInt256.signextend (UInt256.ofNat 12) (withdrawBaseBasic evm src).principal ::
    EVM.word dst.val :: ret :: R) _ _ _ _ _ _ at r10
  have hdp : memLoad (free + ⟨160⟩) (transferBaseReadMemory mem free evm src dst) =
      UInt256.signextend (UInt256.ofNat 12) (withdrawBaseBasic evm dst).principal := hm8.principal
  rw [hdp, signextend104_idem] at r10
  exact ⟨_, _, _, hsrc, hm8, r10⟩

end Benchmarks.CompoundIII.Comet
