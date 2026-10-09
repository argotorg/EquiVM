import Benchmarks.CompoundIII.Comet.TransferAssetModel
import Benchmarks.CompoundIII.Comet.TransferBaseEvm
import Benchmarks.CompoundIII.Comet.TransferCollateralEvm
import Benchmarks.CompoundIII.Comet.Safe128Evm
import Benchmarks.CompoundIII.Comet.BalanceEvm
import Benchmarks.CompoundIII.Comet.DynamicReturnEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_067

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst asset : AccountAddress) (hstack : R.length + 44 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 736 + 1696 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14550⟩
      (solcAddrMask :: EVM.word asset.val :: EVM.word dst.val :: amount ::
        EVM.word src.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, TransferAssetTrace v src dst asset amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have hbase : UInt256.land (wordsOf (immStore v) "baseToken") solcAddrMask = EVM.word v.baseToken.val := by
    rw [wordsOf_immStore_baseToken]
    exact solcAddrMask_clean (addressWord_val_canonical _)
  have hasset : UInt256.land (EVM.word asset.val) solcAddrMask = EVM.word asset.val :=
    solcAddrMask_clean (addressWord_val_canonical _)
  by_cases hb : asset = v.baseToken
  · have r1 := cometWithExtendedAssetList_block_14550_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
      (by rw [hbase, hasset, hb, u256_eq_refl]; decide) h
    by_cases hm : amount = UInt256.lnot ⟨0⟩
    · have r2 := cometWithExtendedAssetList_block_14596_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by rw [hm]; exact u256_sub_self _) r1
      have r3 := cometWithExtendedAssetList_block_14610
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      have hr := cometBalance (v := v) (by change R.length + 4 + 34 ≤ 1024; omega)
        (addressWord_val_canonical src)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have hv : withdrawBalanceValid v evm ↔ CurrentIndicesValid v
          (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee) (timestampWord ee) := by
        rw [withdrawBalanceValid, hs.storageRead, hs.storageRead, hs.env]
        rfl
      by_cases hf : withdrawBalanceValid v evm
      · rw [if_pos (hv.mp hf)] at hr
        obtain ⟨_, _, _, r4⟩ := hr
        have hword : withdrawBalanceWord v evm src = balanceWord v
            (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee) (timestampWord ee)
            (solcSlotWordAt (solcMappingSlot ⟨5⟩ (EVM.word src.val)) σ ee) := by
          rw [withdrawBalanceWord, hs.storageRead, hs.storageRead, hs.storageRead, hs.env]
          rfl
        have r5 := cometWithExtendedAssetList_block_14620
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
        change RD _ _ _ _ _ (EVM.word src.val :: EVM.word dst.val ::
          balanceWord v _ _ _ _ :: UInt256.ofNat 3121 :: ret :: R) _ _ _ _ _ _ at r5
        rw [← hword] at r5
        obtain ⟨result, ht, hr⟩ := cometTransferBase (v := v) src dst
          (by change R.length + 1 + 41 ≤ 1024; omega)
          ((twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide) hmem).trans hfree) hlo
          (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hmem) (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r5
        exact ⟨result, .allBase hb hm hf ht, cometDynamicReturn (by omega) hret hr⟩
      · rw [if_neg (fun he ↦ hf (hv.mpr he))] at hr
        exact ⟨.reverted, .balanceFailed hb hm hf, hr⟩
    · have r2 := cometWithExtendedAssetList_block_14596_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (fun he ↦ hm (u256_sub_eq_zero_iff_eq.mp he))
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      obtain ⟨result, ht, hr⟩ := cometTransferBase (v := v) src dst
        (by change R.length + 1 + 41 ≤ 1024; omega) hfree hlo hmem (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
      exact ⟨result, .base hb hm ht, cometDynamicReturn (by omega) hret hr⟩
  · have hn : EVM.word v.baseToken.val ≠ EVM.word asset.val := by
      intro he
      have ha := congrArg AccountAddress.ofUInt256 he
      change AccountAddress.ofUInt256 (UInt256.ofNat v.baseToken.val) =
        AccountAddress.ofUInt256 (UInt256.ofNat asset.val) at ha
      simp only [accountAddress_roundtrip] at ha
      exact hb ha.symm
    have r1 := cometWithExtendedAssetList_block_14550_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
      (by rw [hbase, hasset, u256_eq_of_ne (Ne.symm hn)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_14626
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    rcases cometSafe128 (v := v) (by change R.length + 5 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2 with
      ⟨hw, _, _, r3⟩ | ⟨hw, hr⟩
    · have r4 := cometWithExtendedAssetList_block_14640
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      obtain ⟨result, ht, hr⟩ := cometTransferCollateral (v := v) src dst asset
        (by change R.length + 1 + 43 ≤ 1024; omega) hw hfree hlo hmem (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r4
      exact ⟨result, .collateral hb hw ht, cometDynamicReturn (by omega) hret hr⟩
    · exact ⟨.reverted, .tooLarge hb hw, hr⟩

end Benchmarks.CompoundIII.Comet
