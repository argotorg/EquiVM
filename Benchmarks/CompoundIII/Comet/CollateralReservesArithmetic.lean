import Benchmarks.CompoundIII.Comet.TotalsCollateralStorage
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_039
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometCollateralSubtract {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {dummy balance ret : UInt256} {R : List UInt256}
    (asset : AccountAddress) (hstack : R.length + 10 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9615⟩
      (dummy :: EVM.word asset.val :: balance :: ret :: R) mem aw rdata σ k C) :
    if (low128 (totalsCollateralWord σ ee asset)).toNat ≤ balance.toNat then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
        (UInt256.sub balance (low128 (totalsCollateralWord σ ee asset)) :: R)
        (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem) = totalsCollateralSlot asset := by
    exact twoWordHashMem_solcMappingSlot_any ⟨2⟩ (EVM.word asset.val) mem
  have hl : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem)) σ ee) =
      low128 (totalsCollateralWord σ ee asset) := by
    rw [hh]
    exact u256_land_comm _ _
  split_ifs with hle
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_9615_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by change UInt256.lt balance (UInt256.land _ (solcSlotWordAt
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem)) σ ee)) = ⟨0⟩
          rw [hl]; exact ult_zero hle) h
    change RD _ _ _ _ _ (balance :: UInt256.land _ (solcSlotWordAt
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem)) σ ee) :: ret :: R)
      (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem) _ _ _ _ _ at r1
    rw [hl] at r1
    have r2 := cometWithExtendedAssetList_block_9649
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    exact ⟨_, _, _, r2⟩
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_9615_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by change UInt256.lt balance (UInt256.land _ (solcSlotWordAt
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem)) σ ee)) ≠ ⟨0⟩
          rw [hl, ult_one (Nat.lt_of_not_ge hle)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7775
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) r2

end Benchmarks.CompoundIII.Comet
