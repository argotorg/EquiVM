import Benchmarks.CompoundIII.Comet.TransferBaseModel
import Benchmarks.CompoundIII.Comet.TransferBaseMathEvm
import Benchmarks.CompoundIII.Comet.TransferBaseTotalsEvm
import Benchmarks.CompoundIII.Comet.TransferBaseUpdateEvm
import Benchmarks.CompoundIII.Comet.TransferBaseTailEvm
import Benchmarks.CompoundIII.Comet.AccrueInternalEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometTransferBaseAfterAccrue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst : AccountAddress) (hstack : R.length + 41 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 736 + 928 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14675⟩
      (EVM.word src.val :: amount :: EVM.word dst.val :: ret :: R) mem aw rdata σ k C) :
    ∃ result, TransferBaseAfterAccrue v src dst amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  obtain ⟨aw1, k1, C1, hsm, hdm, r1⟩ := cometTransferBaseRead (v := v) src dst
    (by omega) hfree hlo hmem (by omega) hs h
  rcases cometTransferBaseMath (v := v) (by omega) hs r1 with
    ⟨hf, k2, C2, r2⟩ | ⟨hf, hr⟩
  · have hW : (withdrawBaseSupplied evm src amount).toNat < 2^104 := withdrawSupplyAmount_lt _ _
    have hS : (supplyBaseSupplied evm dst amount).toNat < 2^104 := supplyAmount_lt _ _
    have hB : (withdrawBaseBorrowed evm src amount).toNat < 2^104 := withdrawBorrowAmount_lt hf.1.2.2
    have hR : (supplyBaseRepaid evm dst amount).toNat < 2^104 := repayAmount_lt hf.2.2.2
    have hr := cometTransferBaseTotals (v := v)
      (supplied := supplyBaseSupplied evm dst amount) (withdrawn := withdrawBaseSupplied evm src amount)
      (borrowed := withdrawBaseBorrowed evm src amount) (repaid := supplyBaseRepaid evm dst amount)
      (by change R.length + 2 + 17 ≤ 1024; omega) hS hW hB hR hs r2
    change internalRun _ _ _ _ _ _ _ _ _ (transferBaseTotals evm src dst amount) at hr
    cases ht : transferBaseTotals evm src dst amount with
    | reverted => rw [ht] at hr; exact ⟨.reverted, .totalsReverted hf ht, hr⟩
    | staticViolation => rw [ht] at hr; exact ⟨.staticViolation, .totalsStatic hf ht, hr⟩
    | ok evm' =>
      rw [ht] at hr
      obtain ⟨σ1, k3, C3, hs1, r3⟩ := hr
      have hp : ee.perm = true := by
        rw [← hs1.env]
        exact transferBaseTotalsOutcome_perm ht
      have h160 : (free + ⟨160⟩).toNat = free.toNat + 160 :=
        uadd_word_ofNat_toNat free 160 (by change _ < 2^256; omega)
      have h320 : (free + ⟨320⟩).toNat = free.toNat + 320 :=
        uadd_word_ofNat_toNat free 320 (by change _ < 2^256; omega)
      have hu := cometTransferBaseUpdate (v := v) src dst
        (by change R.length + 33 ≤ 1024; omega) hsm hdm hlo
        (by omega) (by omega) hs1 r3
      change internalMemoryRun _ _ _ _ _ _ _ _ (transferBaseUpdates v evm evm' src dst amount) at hu
      cases he : transferBaseUpdates v evm evm' src dst amount with
      | reverted => rw [he] at hu; exact ⟨.reverted, .updateReverted hf ht he, hu⟩
      | staticViolation => rw [he] at hu; exact ⟨.staticViolation, .updateStatic hf ht he, hu⟩
      | ok evm'' =>
        rw [he] at hu
        obtain ⟨σ2, aw2, k4, C4, hs2, r4⟩ := hu
        have hsize := transferBaseUpdateMemory_size v evm' src dst
          (withdrawBaseBasic evm src) (withdrawBaseBasic evm dst)
          (withdrawBaseNext evm src amount) (supplyBaseNext evm dst amount)
          hsm hdm hlo (by omega) (by omega)
        have hfree' := (transferBaseUpdateMemory_free v evm' src dst
          (withdrawBaseBasic evm src) (withdrawBaseBasic evm dst)
          (withdrawBaseNext evm src amount) (supplyBaseNext evm dst amount)
          hsm hdm hlo (by omega) (by omega)).trans
            (transferBaseReadMemory_free mem free evm src dst hlo (by change _ < 2^256; omega))
        have hms := hdm.size
        change (free + ⟨160⟩).toNat + 160 ≤ _ at hms
        obtain ⟨result, htail, hr⟩ := cometTransferBaseTail (v := v) src dst hstack hW hS
          hf.1.2.1.1 hp hfree' (by rw [h320]; omega) (by rw [hsize]; omega)
          (by rw [h320, hsize]; omega) (by rw [h320]; omega) hret hs2 r4
        exact ⟨result, .done hf ht he htail, hr⟩
  · exact ⟨.reverted, .mathFailed hf, hr⟩

theorem cometTransferBase {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst : AccountAddress) (hstack : R.length + 41 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 736 + 928 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14664⟩
      (EVM.word src.val :: EVM.word dst.val :: amount :: ret :: R) mem aw rdata σ k C) :
    ∃ result, TransferBaseTrace v src dst amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_14664
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometAccrueInternal (v := v) (by change R.length + 4 + 37 ≤ 1024; omega) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  cases ha : accrueOutcome v evm with
  | reverted => rw [ha] at hr; exact ⟨.reverted, .reverted ha, hr⟩
  | staticViolation => rw [ha] at hr; exact ⟨.staticViolation, .staticViolation ha, hr⟩
  | ok evm' =>
      rw [ha] at hr
      obtain ⟨σ', k', C', hs', r2⟩ := hr
      obtain ⟨result, ht, hr⟩ := cometTransferBaseAfterAccrue (v := v) src dst hstack
        hfree hlo hmem hbound hret hs' r2
      exact ⟨result, .done ha ht, hr⟩

end Benchmarks.CompoundIII.Comet
