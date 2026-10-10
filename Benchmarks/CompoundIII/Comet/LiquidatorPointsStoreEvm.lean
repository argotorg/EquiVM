import Benchmarks.CompoundIII.Comet.LiquidatorPointsMemory
import Benchmarks.CompoundIII.Comet.LiquidatorPointsPacked
import Benchmarks.CompoundIII.Comet.InternalMemoryOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_077

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometStoreLiquidatorPoints {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (addr : AccountAddress) (p : LiquidatorPointsData) (hstack : R.length + 11 ≤ 1024)
    (hm : LiquidatorPointsMemory mem ptr p) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16857⟩
      (liquidatorSlot addr :: ptr :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 mem rdata ret R
      (if evm.executionEnv.perm then .ok (storeLiquidatorPoints evm addr p)
        else .staticViolation) := by
  have r1 := cometWithExtendedAssetList_block_16857
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega) h
  simp only [cometWithExtendedAssetList_block_16857_stack, hm.absorbs, hm.absorbed, hm.spend,
    u256_add_comm (UInt256.ofNat 96) ptr, hm.reserved] at r1
  change RD _ _ _ _ _ (liquidatorSlot addr :: liquidatorPointsPackedWord p :: ret :: R)
    _ _ _ _ _ _ at r1
  cases hp : evm.executionEnv.perm
  · simp only [Bool.false_eq_true, if_false, internalMemoryRun]
    exact r1.sstoreStatic (by rw [← hs.env]; exact hp)
      (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
        wordsOf (immStore v), (⟨16940⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  · simp only [if_true, internalMemoryRun]
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_16940
      (immWords := wordsOf (immStore v)) (by omega) (by rw [← hs.env]; exact hp) hret r1
    exact ⟨_, _, k2, C2, sourceState_liquidatorPoints hs addr p, r2⟩

end Benchmarks.CompoundIII.Comet
