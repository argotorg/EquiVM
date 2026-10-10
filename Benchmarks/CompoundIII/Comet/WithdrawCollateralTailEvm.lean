import Benchmarks.CompoundIII.Comet.WithdrawCollateralMemberEvm
import Benchmarks.CompoundIII.Comet.AssetSearchEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometWithdrawCollateralTail {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount balance next ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (hamount : amount.toNat < 2^128) (hbalance : balance.toNat < 2^128)
    (hnext : next.toNat < 2^128) (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 672 + 1696 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16421⟩
      (withdrawCollateralReadyStack src recipient asset amount balance next ret R)
      mem aw rdata σ k C) :
    ∃ result, WithdrawCollateralTailTrace v src recipient asset amount balance next evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_16421
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨result, ht, hr⟩ := cometAssetSearchInternalBounded (v := v)
    (by change R.length + 11 + 18 ≤ 1024; omega) hfree hlo (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .failed ht, hr⟩
  | some pair =>
    obtain ⟨evm', out⟩ := pair
    obtain ⟨σ', mem', ptr', free', aw', k', C', hs', hv, hm, hb, hg, r2⟩ := hr
    obtain ⟨result, hmember, hr⟩ := cometWithdrawCollateralMember (v := v) src recipient asset
      hstack hamount hbalance hnext hv hm (by omega) (by omega) hret hs' r2
    exact ⟨result, .found ht hv hmember, hr⟩

end Benchmarks.CompoundIII.Comet
