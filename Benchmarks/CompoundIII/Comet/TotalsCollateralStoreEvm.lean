import Benchmarks.CompoundIII.Comet.TotalsCollateralMemory
import Benchmarks.CompoundIII.Comet.CollateralStoreEvm
import Benchmarks.CompoundIII.Comet.High128Write

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometStoreTotalsCollateral {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr total reserved ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (asset : AccountAddress) (hstack : R.length + 12 ≤ 1024)
    (htotal : total.toNat < 2^128) (hm : TotalsCollateralMemory mem ptr total reserved)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13749⟩
      (totalsCollateralSlot asset :: ptr :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 mem rdata ret R
      (if evm.executionEnv.perm then .ok (storeTotalsCollateral evm asset total reserved)
        else .staticViolation) := by
  have hclean : UInt256.land total
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) =
      total := low128_clean total htotal
  have r1 := cometWithExtendedAssetList_block_13749
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_13749_stack, hm.total, hclean] at r1
  have hw := cometStoreLow128 (v := v) (by change R.length + 5 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases hp : evm.executionEnv.perm
  · simpa only [hp, Bool.false_eq_true, if_false, internalMemoryRun] using hw
  · simp only [hp, if_true, internalMemoryRun] at hw ⊢
    obtain ⟨σ', aw', k', C', hs', r2⟩ := hw
    obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_13773
      (immWords := wordsOf (immStore v)) (by omega) (by rw [← hs.env]; exact hp) hret r2
    have hs3 := sourceState_high128Write hs' (totalsCollateralSlot asset) reserved
    simp only [hm.reserved] at r3
    exact ⟨_, _, k3, C3, hs3, r3⟩

end Benchmarks.CompoundIII.Comet
