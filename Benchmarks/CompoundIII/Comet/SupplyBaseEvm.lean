import Benchmarks.CompoundIII.Comet.SupplyBaseModel
import Benchmarks.CompoundIII.Comet.SupplyBaseMathEvm
import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsEvm
import Benchmarks.CompoundIII.Comet.SupplyBaseEventsEvm
import Benchmarks.CompoundIII.Comet.TransferInEvm
import Benchmarks.CompoundIII.Comet.UpdateBaseMemory
import Benchmarks.CompoundIII.Comet.AccrueInternalEvm
import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometSupplyBaseAfterAccrue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst : AccountAddress) (hstack : R.length + 31 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 160 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12473⟩
      (amount :: EVM.word sender.val :: UInt256.ofNat 12591 :: EVM.word dst.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, SupplyBaseAfterAccrue v sender dst amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  obtain ⟨aw1, k1, C1, hm, r1⟩ := cometSupplyBaseRead (v := v) dst
    (by omega) hfree hmem (by omega) hs h
  rcases cometSupplyBaseMath (v := v) (by omega) hs hm.principal r1 with
    ⟨hf, aw2, k2, C2, r2⟩ | ⟨hf, hr⟩
  · have hsupplied : (supplyBaseSupplied evm dst amount).toNat < 2^104 :=
      supplyAmount_lt _ _
    have hrepaid : (supplyBaseRepaid evm dst amount).toNat < 2^104 :=
      repayAmount_lt hf.2.2
    have hr := cometSupplyBaseTotals (v := v)
      (supplied := supplyBaseSupplied evm dst amount)
      (repaid := supplyBaseRepaid evm dst amount)
      (principal := supplyBaseNext evm dst amount)
      (by change R.length + 1 + 19 ≤ 1024; omega) hsupplied hrepaid hs r2
    cases ht : supplyBaseTotalsOutcome evm (supplyBaseSupplied evm dst amount)
        (supplyBaseRepaid evm dst amount) with
    | reverted => rw [ht] at hr; exact ⟨.reverted, .totalsReverted hf ht, hr⟩
    | staticViolation => rw [ht] at hr; exact ⟨.staticViolation, .totalsStatic hf ht, hr⟩
    | ok evm' =>
      rw [ht] at hr
      obtain ⟨σ', k3, C3, hs', r3⟩ := hr
      have hp : ee.perm = true := by
        cases he : evm.executionEnv.perm
        · simp only [supplyBaseTotalsOutcome, he, Bool.false_eq_true, if_false] at ht
          split_ifs at ht
        · simpa only [hs.env] using he
      have r4 := cometWithExtendedAssetList_block_12598
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 9 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      have hu := cometUpdateBasePrincipal (v := v) dst
        (by change R.length + 5 + 25 ≤ 1024; omega) hm hlo hs'
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
      cases he : updateBaseOutcome v evm' dst (withdrawBaseBasic evm dst)
          (supplyBaseNext evm dst amount) with
      | reverted => rw [he] at hu; exact ⟨.reverted, .updateReverted hf ht he, hu⟩
      | staticViolation => rw [he] at hu; exact ⟨.staticViolation, .updateStatic hf ht he, hu⟩
      | ok evm'' =>
        rw [he] at hu
        obtain ⟨σ'', aw5, k5, C5, hs'', r5⟩ := hu
        obtain ⟨mem6, aw6, k6, C6, r6⟩ := cometSupplyBaseEvents (v := v)
          (by change R.length + 13 ≤ 1024; omega) hsupplied hp hret r5
        exact ⟨.ok evm'', .done hf ht he, σ'', mem6, aw6, rdata, k6, C6, hs'', r6⟩
  · exact ⟨.reverted, .mathFailed hf, hr⟩

theorem cometSupplyBaseAfterTransfer {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst : AccountAddress) (hstack : R.length + 42 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 160 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12465⟩
      (amount :: EVM.word sender.val :: UInt256.ofNat 12591 :: EVM.word dst.val :: ret :: R) mem aw rdata σ k C) :
    ∃ result, SupplyBaseAfterTransfer v sender dst amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_12465
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometAccrueInternal (v := v) (by change R.length + 5 + 37 ≤ 1024; omega) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  cases ha : accrueOutcome v evm with
  | reverted => rw [ha] at hr; exact ⟨.reverted, .reverted ha, hr⟩
  | staticViolation => rw [ha] at hr; exact ⟨.staticViolation, .staticViolation ha, hr⟩
  | ok evm' =>
    rw [ha] at hr
    obtain ⟨σ', k', C', hs', r2⟩ := hr
    obtain ⟨result, ht, hr⟩ := cometSupplyBaseAfterAccrue (v := v) sender dst (by omega)
      hfree hlo hmem hbound hret hs' r2
    exact ⟨result, .done ha ht, hr⟩

theorem cometSupplyBase {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst : AccountAddress) (hstack : R.length + 42 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 224 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12418⟩
      (EVM.word sender.val :: EVM.word dst.val :: amount :: ret :: R) mem aw rdata σ k C) :
    ∃ result, SupplyBaseTrace v sender dst amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_12418
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_12418_stack, wordsOf_immStore_baseToken] at r1
  obtain ⟨result, ht, hr⟩ := cometTransferInInternal (v := v)
    (by change R.length + 4 + 16 ≤ 1024; omega) hfree hlo (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .transferFailed ht, hr⟩
  | some result =>
    obtain ⟨evm', received⟩ := result
    obtain ⟨σ', mem', aw', out, k', C', hs', hfree', hmem', r2⟩ := hr
    have hn : (free + ⟨64⟩).toNat = free.toNat + 64 :=
      uadd_word_ofNat_toNat free 64 (by change free.toNat + 64 < 2^256; omega)
    obtain ⟨result, tail, hr⟩ := cometSupplyBaseAfterTransfer (v := v) sender dst hstack
      hfree' (by omega) (by omega) (by omega) hret hs' r2
    exact ⟨result, .transferOk ht tail, hr⟩

end Benchmarks.CompoundIII.Comet
