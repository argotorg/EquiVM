import Benchmarks.CompoundIII.Comet.TwoAddressDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def permissionRuntimeWord (σ : AccountMap) (I : ExecutionEnv) (owner manager : UInt256) : UInt256 :=
  if owner = manager then ⟨1⟩ else
    UInt256.land (solcSlotWordAt (solcMappingSlot (solcMappingSlot ⟨3⟩ owner) manager) σ I) ⟨255⟩

def permissionMemory (owner manager : UInt256) (mem : ByteArray) : ByteArray :=
  if owner = manager then mem else
    twoWordHashMem manager (solcMappingSlot ⟨3⟩ owner) (twoWordHashMem owner ⟨3⟩ mem)

theorem permissionMemory_size (owner manager : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (permissionMemory owner manager mem).size = 96 := by
  unfold permissionMemory
  split
  · exact hmem
  · exact twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ hmem)

theorem permissionMemory_read64 (owner manager : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    (permissionMemory owner manager mem).readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  unfold permissionMemory
  split
  · exact hread
  · exact twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ hmem)
      (twoWordHashMem_read64 _ _ hmem hread)

theorem cometHasPermission {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {owner manager ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (ho : owner.toNat < EVM.addressModulus) (hm : manager.toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨6921⟩ (owner :: manager :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (permissionRuntimeWord σ ee owner manager :: R) (permissionMemory owner manager mem)
      aw' rdata σ k' C' := by
  have hoClean : UInt256.land owner (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) = owner :=
    solcAddrMask_clean ho
  have hmClean : UInt256.land manager (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) = manager :=
    solcAddrMask_clean hm
  by_cases heq : owner = manager
  · have rd1 := cometWithExtendedAssetList_block_6921_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by rw [hoClean, hmClean, heq, uInt256_eq_self]; rfl) h
    unfold cometWithExtendedAssetList_block_6921_fallthrough_stack at rd1
    rw [hoClean, hmClean, heq, uInt256_eq_self] at rd1
    have rd2 := cometWithExtendedAssetList_block_6946
      (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
    simp only [permissionRuntimeWord, permissionMemory, heq, if_true]
    exact ⟨_, _, _, rd2⟩
  · have heqWord : UInt256.eq owner manager = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ heq (uInt256_eq_one_eq h))
    have rd1 := cometWithExtendedAssetList_block_6921_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by rw [hoClean, hmClean, heqWord]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    unfold cometWithExtendedAssetList_block_6921_taken_stack at rd1
    rw [hoClean, hmClean, heqWord] at rd1
    have rd2 := cometWithExtendedAssetList_block_6950
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    let mem₀ := twoWordHashMem owner ⟨3⟩ mem
    let slot₀ := solcMappingSlot ⟨3⟩ owner
    have hhash₀ : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₀ = slot₀ :=
      twoWordHashMem_solcMappingSlot_any ⟨3⟩ owner mem
    change RD _ _ _ _ _
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₀ :: manager :: ⟨6977⟩ :: ⟨255⟩ :: ret :: R)
      mem₀ _ _ _ _ _ at rd2
    rw [hhash₀] at rd2
    have rd3 := cometWithExtendedAssetList_block_2428
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hmCleanLeft : UInt256.land (UInt256.sub
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) manager = manager :=
      solcAddrMask_clean_left hm
    unfold cometWithExtendedAssetList_block_2428_stack cometWithExtendedAssetList_block_2428_memory at rd3
    rw [hmCleanLeft] at rd3
    let mem₁ := twoWordHashMem manager slot₀ mem₀
    have hhash₁ : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁ =
        solcMappingSlot slot₀ manager := twoWordHashMem_solcMappingSlot_any slot₀ manager mem₀
    change RD _ _ _ _ _ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁ :: ⟨255⟩ :: ret :: R)
      mem₁ _ _ _ _ _ at rd3
    rw [hhash₁] at rd3
    obtain ⟨k₄, C₄, rd4⟩ := cometWithExtendedAssetList_block_6977
      (immWords := wordsOf (immStore v)) (by omega) hvalid rd3
    simp only [permissionRuntimeWord, permissionMemory, heq, if_false]
    exact ⟨_, _, _, rd4⟩

end Benchmarks.CompoundIII.Comet
