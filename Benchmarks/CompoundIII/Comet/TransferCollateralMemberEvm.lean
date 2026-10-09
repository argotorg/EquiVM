import Benchmarks.CompoundIII.Comet.TransferCollateralCheckEvm
import Benchmarks.CompoundIII.Comet.AssetMembershipEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferCollateralDstMember {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr free amount balance next ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (src dst asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (hb : balance.toNat < 2^128) (hn : next.toNat < 2^128)
    (hv : AssetValid out) (hm : AssetMemory mem ptr free out) (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15523⟩
      (transferCollateralDstStack src dst asset ptr amount balance next ret R) mem aw out σ k C) :
    ∃ result, TransferCollateralDstMember v src dst balance next evm out result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_15523
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hoffset : memLoad ptr mem = calldataWord out 0 := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      uint256_add_zero_right] using hm.words 0 (by decide)
  obtain ⟨mem', hshape, hr⟩ := cometUpdateAssetsIn (v := v) dst
    (by change R.length + 7 + 14 ≤ 1024; omega) hoffset hv.2.1 hb hn
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  obtain ⟨hm', hsize⟩ := hm.scratchOrSame _ _ hshape
  cases he : assetMembershipResult evm dst (calldataWord out 0) balance next with
  | reverted => rw [he] at hr; exact ⟨.reverted, .reverted he, hr⟩
  | staticViolation => rw [he] at hr; exact ⟨.staticViolation, .staticViolation he, hr⟩
  | ok evm' =>
    rw [he] at hr
    obtain ⟨σ', aw', k', C', hs', r2⟩ := hr
    obtain ⟨result, ht, hr⟩ := cometTransferCollateralCheck src dst asset hstack hm'.freeWord
      (by have hl := hm'.lower; have hp := hm'.separate; omega)
      (by have hl := hm'.lower; have hp := hm'.present; omega)
      (by rw [hsize]; exact hgap) hbound hret hs' r2
    exact ⟨result, .done he ht, hr⟩

theorem cometTransferCollateralSrcMember {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr free amount srcBalance srcNext dstBalance dstNext ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (hsb : srcBalance.toNat < 2^128) (hsn : srcNext.toNat < 2^128)
    (hdb : dstBalance.toNat < 2^128) (hdn : dstNext.toNat < 2^128)
    (hv : AssetValid out) (hm : AssetMemory mem ptr free out) (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15511⟩
      (ptr :: transferCollateralReadyStack src dst asset amount
        srcBalance srcNext dstBalance dstNext ret R) mem aw out σ k C) :
    ∃ result, TransferCollateralSrcMember v src dst srcBalance srcNext dstBalance dstNext
        evm out result ∧ internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_15511
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 11 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hoffset : memLoad ptr mem = calldataWord out 0 := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      uint256_add_zero_right] using hm.words 0 (by decide)
  obtain ⟨mem', hshape, hr⟩ := cometUpdateAssetsIn (v := v) src
    (by change R.length + 11 + 14 ≤ 1024; omega) hoffset hv.2.1 hsb hsn
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  obtain ⟨hm', hsize⟩ := hm.scratchOrSame _ _ hshape
  cases he : assetMembershipResult evm src (calldataWord out 0) srcBalance srcNext with
  | reverted => rw [he] at hr; exact ⟨.reverted, .reverted he, hr⟩
  | staticViolation => rw [he] at hr; exact ⟨.staticViolation, .staticViolation he, hr⟩
  | ok evm' =>
    rw [he] at hr
    obtain ⟨σ', aw', k', C', hs', r2⟩ := hr
    obtain ⟨result, ht, hr⟩ := cometTransferCollateralDstMember src dst asset hstack
      hdb hdn hv hm' (by rw [hsize]; exact hgap) hbound hret hs' r2
    exact ⟨result, .done he ht, hr⟩

end Benchmarks.CompoundIII.Comet
