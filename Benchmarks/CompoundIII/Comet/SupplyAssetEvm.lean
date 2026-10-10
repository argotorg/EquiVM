import Benchmarks.CompoundIII.Comet.SupplyAssetModel
import Benchmarks.CompoundIII.Comet.SupplyBaseEvm
import Benchmarks.CompoundIII.Comet.SupplyCollateralEvm
import Benchmarks.CompoundIII.Comet.Safe128Evm
import Benchmarks.CompoundIII.Comet.BorrowBalanceEvm
import Benchmarks.CompoundIII.Comet.DynamicReturnEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst asset : AccountAddress) (hstack : R.length + 44 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 576 + 768 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12105⟩
      (EVM.word asset.val :: EVM.word dst.val :: amount :: EVM.word sender.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, SupplyAssetTrace v sender dst asset amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have hbase : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1)) (wordsOf (immStore v) "baseToken") = EVM.word v.baseToken.val := by
    rw [wordsOf_immStore_baseToken]
    exact solcAddrMask_clean_left (addressWord_val_canonical _)
  have hasset : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1)) (EVM.word asset.val) = EVM.word asset.val :=
    solcAddrMask_clean_left (addressWord_val_canonical _)
  by_cases hb : asset = v.baseToken
  · have r1 := cometWithExtendedAssetList_block_12105_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
      (by rw [hbase, hasset, hb]; exact u256_sub_self _) h
    by_cases hm : amount = UInt256.lnot ⟨0⟩
    · have r2 := cometWithExtendedAssetList_block_12157_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by rw [hm]; exact u256_sub_self _) r1
      have r3 := cometWithExtendedAssetList_block_12171
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      have hr := cometBorrowBalance (v := v) (by change R.length + 4 + 34 ≤ 1024; omega)
        (addressWord_val_canonical dst)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have hv : supplyBorrowValid v evm dst ↔ BorrowBalanceValid v
          (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee) (timestampWord ee)
          (solcSlotWordAt (solcMappingSlot ⟨5⟩ (EVM.word dst.val)) σ ee) := by
        rw [supplyBorrowValid, hs.storageRead, hs.storageRead, hs.storageRead, hs.env]
        rfl
      by_cases hf : supplyBorrowValid v evm dst
      · rw [if_pos (hv.mp hf)] at hr
        obtain ⟨_, _, _, r4⟩ := hr
        have hword : supplyBorrowWord v evm dst = borrowBalanceWord v
            (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee) (timestampWord ee)
            (solcSlotWordAt (solcMappingSlot ⟨5⟩ (EVM.word dst.val)) σ ee) := by
          rw [supplyBorrowWord, hs.storageRead, hs.storageRead, hs.storageRead, hs.env]
          rfl
        have r5 := cometWithExtendedAssetList_block_12181
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
        change RD _ _ _ _ _ (EVM.word sender.val :: EVM.word dst.val ::
          borrowBalanceWord v _ _ _ _ :: UInt256.ofNat 3121 :: ret :: R) _ _ _ _ _ _ at r5
        rw [← hword] at r5
        obtain ⟨result, ht, hr⟩ := cometSupplyBase (v := v) sender dst
          (by change R.length + 1 + 42 ≤ 1024; omega)
          ((twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide) hmem).trans hfree) hlo (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r5
        exact ⟨result, .allBase hb hm hf ht, cometDynamicReturn (by omega) hret hr⟩
      · rw [if_neg (fun he ↦ hf (hv.mpr he))] at hr
        exact ⟨.reverted, .balanceFailed hb hm hf, hr⟩
    · have r2 := cometWithExtendedAssetList_block_12157_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (fun he ↦ hm (u256_sub_eq_zero_iff_eq.mp he))
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      obtain ⟨result, ht, hr⟩ := cometSupplyBase (v := v) sender dst
        (by change R.length + 1 + 42 ≤ 1024; omega) hfree hlo (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
      exact ⟨result, .base hb hm ht, cometDynamicReturn (by omega) hret hr⟩
  · have hn : EVM.word v.baseToken.val ≠ EVM.word asset.val := by
      intro he
      have ha := congrArg AccountAddress.ofUInt256 he
      change AccountAddress.ofUInt256 (UInt256.ofNat v.baseToken.val) =
        AccountAddress.ofUInt256 (UInt256.ofNat asset.val) at ha
      simp only [accountAddress_roundtrip] at ha
      exact hb ha.symm
    have r1 := cometWithExtendedAssetList_block_12105_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
      (by rw [hbase, hasset]; exact fun he ↦ hn (u256_sub_eq_zero_iff_eq.mp he))
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_12187
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    rcases cometSafe128 (v := v) (by change R.length + 5 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2 with
      ⟨hw, _, _, r3⟩ | ⟨hw, hr⟩
    · have r4 := cometWithExtendedAssetList_block_12201
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      obtain ⟨result, ht, hr⟩ := cometSupplyCollateral (v := v) sender dst asset
        (by change R.length + 1 + 30 ≤ 1024; omega) hw hfree hlo hbound
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r4
      exact ⟨result, .collateral hb hw ht, cometDynamicReturn (by omega) hret hr⟩
    · exact ⟨.reverted, .tooLarge hb hw, hr⟩

end Benchmarks.CompoundIII.Comet
