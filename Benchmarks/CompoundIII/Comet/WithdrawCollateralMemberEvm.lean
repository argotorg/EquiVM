import Benchmarks.CompoundIII.Comet.WithdrawCollateralCheckEvm
import Benchmarks.CompoundIII.Comet.WithdrawCollateralWrite
import Benchmarks.CompoundIII.Comet.AssetMembershipEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometWithdrawCollateralMember {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr free amount balance next ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (src recipient asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (hamount : amount.toNat < 2^128) (hbalance : balance.toNat < 2^128)
    (hnext : next.toNat < 2^128) (hv : AssetValid out) (hm : AssetMemory mem ptr free out)
    (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16430⟩
      (ptr :: withdrawCollateralReadyStack src recipient asset amount balance next ret R)
      mem aw out σ k C) :
    ∃ result, WithdrawCollateralMember v src recipient asset amount balance next evm out result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_16430
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hword : memLoad ptr mem = calldataWord out 0 := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      uint256_add_zero_right] using hm.words 0 (by decide)
  obtain ⟨mem', hshape, hr⟩ := cometUpdateAssetsIn (v := v) src
    (by change R.length + 9 + 14 ≤ 1024; omega) hword hv.2.1 hbalance hnext
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  obtain ⟨hm', hsize⟩ := hm.scratchOrSame _ _ hshape
  have hfree := hm'.freeWord
  cases he : assetMembershipResult evm src (calldataWord out 0) balance next with
  | reverted => rw [he] at hr; exact ⟨.reverted, .reverted he, hr⟩
  | staticViolation => rw [he] at hr; exact ⟨.staticViolation, .staticViolation he, hr⟩
  | ok evm' =>
    rw [he] at hr
    obtain ⟨σ', aw', k', C', hs', r2⟩ := hr
    obtain ⟨result, ht, hr⟩ := cometWithdrawCollateralCheck (v := v) src recipient asset hstack
      hamount hfree (by have hl := hm.lower; have hp := hm.separate; omega)
      (by rw [hsize]; have hl := hm.lower; have hp := hm.present; omega)
      (by rw [hsize]; exact hgap) hbound hret hs' r2
    exact ⟨result, .done he ht, hr⟩

end Benchmarks.CompoundIII.Comet
