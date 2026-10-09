import Benchmarks.CompoundIII.Comet.AbsorbFinishModel
import Benchmarks.CompoundIII.Comet.AbsorbSettlementEvm
import Benchmarks.CompoundIII.Comet.PrincipalValueEvm
import Benchmarks.CompoundIII.Comet.UpdateBaseMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104 updateBaseOutcome

theorem cometAbsorbFinish {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw old next price absorber ret ptr free : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (account : AccountAddress) (basic : UserBasicData)
    (hstack : R.length + 34 ≤ 1024) (hn : next.toNat < 2^255)
    (hbasic : UserBasicMemory mem ptr basic) (hptr : 96 ≤ ptr.toNat)
    (hf : memLoad ⟨64⟩ mem = free) (hl : 96 ≤ free.toNat) (hm : free.toNat ≤ mem.size)
    (hb : free.toNat + 64 < UInt256.size) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17240⟩
      (basic.principal :: old :: next :: price :: EVM.word account.val :: collateralBaseScale v ::
        ptr :: absorber :: ret :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbFinishTrace v evm account basic old next price result ∧
      internalPreservingRun (deployedRuntime v) ee g s0 mem free rdata ret R result := by
  have r1 := cometWithExtendedAssetList_block_17240 (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  rcases cometPrincipalValue (v := v) (by change R.length + 9 + 12 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1 with
    ⟨hp, k2, C2, r2⟩ | ⟨hp, hr⟩
  · have r3 := cometWithExtendedAssetList_block_17249 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 12 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have hr := cometUpdateBasePrincipal (v := v) account
      (by change R.length + 9 + 25 ≤ 1024; omega) hbasic hptr hs
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    cases hu : updateBaseOutcome v evm account basic (principalValueWord evm next) with
    | reverted =>
      rw [hu] at hr
      exact ⟨.reverted, .updateReverted hp hu, hr⟩
    | staticViolation =>
      rw [hu] at hr
      exact ⟨.staticViolation, .updateStatic hp hu, hr⟩
    | ok updated =>
      rw [hu] at hr
      obtain ⟨σ4, aw4, k4, C4, hs4, r4⟩ := hr
      have hperm : ee.perm = true := by rw [← hs.env]; exact updateBaseOutcome_ok_perm hu
      have hsize := updateBaseMemory_size v evm account basic (principalValueWord evm next) hbasic hptr
      have hfree := (updateBaseMemory_free v evm account basic
        (principalValueWord evm next) hbasic hptr).trans hf
      obtain ⟨result, ht, hr⟩ := cometAbsorbSettlement (v := v) account (by omega) hn
        (principalValueWord_nonneg_lt hp ((signedWord_nonneg_iff next).2 hn)) hperm
        hfree hl (by rw [hsize]; exact hm) hb hs4 hret r4
      exact ⟨result, .settled hp hu ht, hr.of_size_eq hsize.symm⟩
  · exact ⟨.reverted, .principalReverted hp, hr⟩

end Benchmarks.CompoundIII.Comet
