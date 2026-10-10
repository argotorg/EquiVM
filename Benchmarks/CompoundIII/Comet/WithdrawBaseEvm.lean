import Benchmarks.CompoundIII.Comet.WithdrawBaseModel
import Benchmarks.CompoundIII.Comet.WithdrawBaseMathEvm
import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsEvm
import Benchmarks.CompoundIII.Comet.WithdrawBaseTailEvm
import Benchmarks.CompoundIII.Comet.UpdateBaseMemory
import Benchmarks.CompoundIII.Comet.AccrueInternalEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometWithdrawBaseAfterAccrue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient : AccountAddress) (hstack : R.length + 41 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 576 + 928 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15748⟩
      (EVM.word recipient.val :: amount :: EVM.word src.val :: UInt256.ofNat 12591 :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, WithdrawBaseAfterAccrue v src recipient amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  obtain ⟨aw1, k1, C1, hm, r1⟩ := cometWithdrawBaseRead (v := v) src
    (by change R.length + 1 + 13 ≤ 1024; omega) hfree hmem (by omega) hs h
  rcases cometWithdrawBaseMath (v := v) (by change R.length + 1 + 22 ≤ 1024; omega) hs r1 with
    ⟨hf, k2, C2, r2⟩ | ⟨hf, hr⟩
  · have hsupplied : (withdrawBaseSupplied evm src amount).toNat < 2^104 :=
      withdrawSupplyAmount_lt _ _
    have hborrowed : (withdrawBaseBorrowed evm src amount).toNat < 2^104 :=
      withdrawBorrowAmount_lt hf.2.2
    have hr := cometWithdrawBaseTotals (v := v)
      (supplied := withdrawBaseSupplied evm src amount)
      (borrowed := withdrawBaseBorrowed evm src amount)
      (principal := withdrawBaseNext evm src amount)
      (by change R.length + 1 + 19 ≤ 1024; omega) hsupplied hborrowed hs r2
    cases ht : withdrawBaseTotalsOutcome evm (withdrawBaseSupplied evm src amount)
        (withdrawBaseBorrowed evm src amount) with
    | reverted => rw [ht] at hr; exact ⟨.reverted, .totalsReverted hf ht, hr⟩
    | staticViolation => rw [ht] at hr; exact ⟨.staticViolation, .totalsStatic hf ht, hr⟩
    | ok evm' =>
      rw [ht] at hr
      obtain ⟨σ', k3, C3, hs', r3⟩ := hr
      have hp : ee.perm = true := by
        cases he : evm.executionEnv.perm
        · simp only [withdrawBaseTotalsOutcome, he, Bool.false_eq_true, if_false] at ht
          split_ifs at ht <;> cases ht
        · simpa only [hs.env] using he
      have r4 := cometWithExtendedAssetList_block_12598
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 9 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      have hu := cometUpdateBasePrincipal (v := v) src
        (by change R.length + 6 + 25 ≤ 1024; omega) hm hlo hs'
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
      cases he : updateBaseOutcome v evm' src (withdrawBaseBasic evm src)
          (withdrawBaseNext evm src amount) with
      | reverted => rw [he] at hu; exact ⟨.reverted, .updateReverted hf ht he, hu⟩
      | staticViolation => rw [he] at hu; exact ⟨.staticViolation, .updateStatic hf ht he, hu⟩
      | ok evm'' =>
        rw [he] at hu
        obtain ⟨σ'', aw5, k5, C5, hs'', r5⟩ := hu
        have hsize := updateBaseMemory_size v evm' src (withdrawBaseBasic evm src)
          (withdrawBaseNext evm src amount) hm hlo
        have hfree' := (updateBaseMemory_free v evm' src (withdrawBaseBasic evm src)
          (withdrawBaseNext evm src amount) hm hlo).trans
            (withdrawBaseReadMemory_free _ _ _ _ hlo (by change _ < 2^256; omega))
        have hn : (free + ⟨160⟩).toNat = free.toNat + 160 :=
          uadd_word_ofNat_toNat free 160 (by change free.toNat + 160 < 2^256; omega)
        have hms := hm.size
        obtain ⟨result, htail, hr⟩ := cometWithdrawBaseTail (v := v) src recipient hstack
          hsupplied hf.2.1.1 hp hfree' (by rw [hn]; omega)
          (by rw [hsize]; omega) (by rw [hn, hsize]; omega)
          (by rw [hn]; omega) hret hs'' r5
        exact ⟨result, .done hf ht he htail, hr⟩
  · exact ⟨.reverted, .mathFailed hf, hr⟩

theorem cometWithdrawBase {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient : AccountAddress) (hstack : R.length + 42 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 576 + 928 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15734⟩
      (EVM.word src.val :: EVM.word recipient.val :: amount :: ret :: R) mem aw rdata σ k C) :
    ∃ result, WithdrawBaseTrace v src recipient amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_15734
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometAccrueInternal (v := v) (by change R.length + 5 + 37 ≤ 1024; omega) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  cases ha : accrueOutcome v evm with
  | reverted => rw [ha] at hr; exact ⟨.reverted, .reverted ha, hr⟩
  | staticViolation => rw [ha] at hr; exact ⟨.staticViolation, .staticViolation ha, hr⟩
  | ok evm' =>
    rw [ha] at hr
    obtain ⟨σ', k', C', hs', r2⟩ := hr
    obtain ⟨result, ht, hr⟩ := cometWithdrawBaseAfterAccrue (v := v) src recipient (by omega)
      hfree hlo hmem hbound hret hs' r2
    exact ⟨result, .done ha ht, hr⟩

end Benchmarks.CompoundIII.Comet
