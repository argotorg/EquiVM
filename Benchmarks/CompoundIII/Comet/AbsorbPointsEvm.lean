import Benchmarks.CompoundIII.Comet.AbsorbPointsCountsEvm
import Benchmarks.CompoundIII.Comet.AbsorbPointsSpendEvm
import Benchmarks.CompoundIII.Comet.LiquidatorPointsAllocation
import Benchmarks.CompoundIII.Comet.LiquidatorPointsStoreEvm
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbPoints {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr n gasUsed ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (addr : AccountAddress) (hstack : R.length + 20 ≤ 1024) (hn : n.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hmem : 96 ≤ mem.size)
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 128 < 2^64)
    (hs : SourceState s0 ee σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16733⟩
      (gasUsed :: ⟨13846⟩ :: ⟨16819⟩ :: ⟨16850⟩ :: EVM.word addr.val :: ⟨16857⟩ ::
        n :: ⟨3121⟩ :: ret :: R) mem aw rdata σ k C) :
    internalDynamicRun (deployedRuntime v) ee g s0 ret R
      (absorbPointsOutcome evm addr n gasUsed) := by
  let p := absorbPointsLoaded evm addr
  let fee := UInt256.ofNat ee.header.baseFeePerGas
  have hp : p = liquidatorPointsData (solcSlotWordAt (liquidatorSlot addr) σ ee) := by
    dsimp only [p, absorbPointsLoaded]
    rw [hs.storageRead]
    rfl
  have ha : p.absorbs.toNat < 2^32 := by
    rw [hp]
    exact liquidatorPointsData_bound _ 0
  have hac : p.absorbed.toNat < 2^64 := by
    rw [hp]
    exact liquidatorPointsData_bound _ 1
  have hsp : p.spend.toNat < 2^128 := by
    rw [hp]
    exact liquidatorPointsData_bound _ 2
  have r1 := cometWithExtendedAssetList_block_16733
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 12 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 12 + 6 ≤ 1024; omega) (addressWord_val_canonical addr)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_16753
    (immWords := wordsOf (immStore v)) (by change R.length + 13 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, hm4, r4⟩ := cometAllocateLiquidatorPoints (v := v)
    (by change R.length + 11 + 9 ≤ 1024; omega)
    (by rw [twoWordHashMem_load_ge (ptr := UInt256.ofNat 64) _ _ (by decide) hmem]; exact hfree)
    hb (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  change LiquidatorPointsMemory _ ptr (liquidatorPointsData (solcSlotWordAt (liquidatorSlot addr) σ ee)) at hm4
  rw [← hp] at hm4
  have hcounts := cometAbsorbPointsCounts (v := v) (by omega) hm4 ha hac hn r4
  simp only [absorbPointsOutcome, hs.env]
  change internalDynamicRun _ _ _ _ _ _
    (if AbsorbPointsValid p n gasUsed fee then
      if ee.perm then .ok (storeLiquidatorPoints evm addr
        (absorbPointsSpend (absorbPointsCounts p n) gasUsed fee)) else .staticViolation
    else .reverted)
  by_cases hc : p.absorbs.toNat + 1 < 2^32 ∧ p.absorbed.toNat + n.toNat < 2^64
  · rw [if_pos hc] at hcounts
    obtain ⟨mem5, aw5, k5, C5, hm5, r5⟩ := hcounts
    have hspend := cometAbsorbPointsSpend (v := v) (by omega) hm5 hsp r5
    change (if AbsorbPointsSpendValid p gasUsed fee then _ else _) at hspend
    by_cases hspv : AbsorbPointsSpendValid p gasUsed fee
    · rw [if_pos hspv] at hspend
      rw [if_pos (show AbsorbPointsValid p n gasUsed fee from ⟨hc, hspv⟩)]
      obtain ⟨mem6, aw6, k6, C6, hm6, r6⟩ := hspend
      have r7 := cometWithExtendedAssetList_block_16850
        (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      obtain ⟨aw8, k8, C8, r8⟩ := cometMappingHash (v := v)
        (by change R.length + 3 + 6 ≤ 1024; omega) (addressWord_val_canonical addr)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
      have hm8 := hm6.scratch hlo (EVM.word addr.val) ⟨7⟩
      have hw := cometStoreLiquidatorPoints (v := v) addr _
        (by change R.length + 1 + 11 ≤ 1024; omega) hm8 hs
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
      rw [hs.env] at hw
      cases hpv : ee.perm
      · simpa only [hpv, Bool.false_eq_true, if_false, internalMemoryRun, internalDynamicRun] using hw
      · simp only [hpv, if_true, internalMemoryRun] at hw
        simp only [if_true, internalDynamicRun]
        obtain ⟨σ9, aw9, k9, C9, hs9, r9⟩ := hw
        have r10 := cometWithExtendedAssetList_block_3121
          (immWords := wordsOf (immStore v)) (by omega) hret r9
        exact ⟨_, _, _, _, _, _, hs9, r10⟩
    · rw [if_neg hspv] at hspend
      rw [if_neg (show ¬ AbsorbPointsValid p n gasUsed fee from fun hv ↦ hspv hv.2)]
      exact hspend
  · rw [if_neg hc] at hcounts
    rw [if_neg (show ¬ AbsorbPointsValid p n gasUsed fee from fun hv ↦ hc hv.1)]
    exact hcounts

end Benchmarks.CompoundIII.Comet
