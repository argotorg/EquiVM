import Benchmarks.CompoundIII.Comet.TransferCollateralStacks
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_071

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferCollateralRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst asset : AccountAddress) (hstack : R.length + 16 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15329⟩
      (EVM.word src.val :: EVM.word dst.val :: EVM.word asset.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15305⟩
      (transferCollateralSubStack src dst asset amount
        (withdrawCollateralBalance evm src asset) (withdrawCollateralBalance evm dst asset) ret R)
      (transferCollateralMemory mem src dst asset) aw' rdata σ k' C' := by
  have hclean (account : AccountAddress) : UInt256.land (EVM.word account.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = EVM.word account.val := addressWord_val_clean account
  have r1 := cometWithExtendedAssetList_block_15329
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 11 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_15329_stack,
    cometWithExtendedAssetList_block_15329_memory, hclean] at r1
  change RD _ _ _ _ _
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.word src.val) ⟨6⟩ mem) :: _)
    (twoWordHashMem (EVM.word src.val) ⟨6⟩ mem) _ _ _ _ _ at r1
  have hhashSrc : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.word src.val) ⟨6⟩ mem) =
      solcMappingSlot ⟨6⟩ (EVM.word src.val) :=
    twoWordHashMem_solcMappingSlot_any ⟨6⟩ (EVM.word src.val) mem
  rw [hhashSrc] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 9 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_15382
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 12 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [cometWithExtendedAssetList_block_15382_stack,
    cometWithExtendedAssetList_block_15382_memory, hclean] at r3
  change RD _ _ _ _ _
    (keccakWord ⟨0⟩ ⟨64⟩
      (twoWordHashMem (EVM.word dst.val) ⟨6⟩ (userCollateralMemory mem src asset)) :: _)
    (twoWordHashMem (EVM.word dst.val) ⟨6⟩ (userCollateralMemory mem src asset)) _ _ _ _ _ at r3
  have hhashDst : keccakWord ⟨0⟩ ⟨64⟩
      (twoWordHashMem (EVM.word dst.val) ⟨6⟩ (userCollateralMemory mem src asset)) =
      solcMappingSlot ⟨6⟩ (EVM.word dst.val) :=
    twoWordHashMem_solcMappingSlot_any ⟨6⟩ (EVM.word dst.val) _
  rw [hhashDst] at r3
  obtain ⟨aw4, k4, C4, r4⟩ := cometMappingHash (v := v)
    (by change R.length + 10 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  obtain ⟨k5, C5, r5⟩ := cometWithExtendedAssetList_block_15413
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 13 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  change RD _ _ _ _ _ (transferCollateralSubStack src dst asset amount
    (low128 (solcSlotWord σ ee (userCollateralSlot src asset)))
    (low128 (solcSlotWord σ ee (userCollateralSlot dst asset))) ret R) _ _ _ _ _ _ at r5
  rw [← hs.storageRead, ← hs.storageRead] at r5
  exact ⟨_, _, _, r5⟩

end Benchmarks.CompoundIII.Comet
