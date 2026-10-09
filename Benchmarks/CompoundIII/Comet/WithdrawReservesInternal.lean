import Benchmarks.CompoundIII.Comet.WithdrawReservesModel
import Benchmarks.CompoundIII.Comet.WithdrawReservesLog
import Benchmarks.CompoundIII.Comet.TransferOutInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def WithdrawReservesRun (v : CometWithExtendedAssetListImmutables)
    (g : Sat256) (s0 : State) (result : Option EVM.State) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some evm' => if evm'.executionEnv.perm = true then
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty
    else RDstatic (deployedRuntime v) g s0

theorem cometWithdrawReservesAfter {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {free reserves amount mask : UInt256} {R : List UInt256}
    {recipient : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 21 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = free)
    (hlo : 96 ≤ free.toNat) (hb : free.toNat + 68 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6208⟩
      (reserves :: mask :: EVM.word recipient.val :: amount :: R) mem aw rdata σ k C) :
    ∃ result, WithdrawReservesAfter v recipient amount reserves evm result ∧
      WithdrawReservesRun v g s0 result := by
  rcases cometWithdrawReservesChecks (by omega) h with ⟨hv, k1, C1, r1⟩ | ⟨hv, r1⟩
  · have r2 := cometWithExtendedAssetList_block_6226
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [cometWithExtendedAssetList_block_6226_stack, wordsOf_immStore_baseToken] at r2
    obtain ⟨result, ht, hr⟩ := cometTransferOutInternal (v := v)
      (by change R.length + 4 + 17 ≤ 1024; omega) hfree hlo hb
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
    refine ⟨result, .transfer hv ht, ?_⟩
    cases result with
    | none => exact hr
    | some evm' =>
      obtain ⟨σ', mem', aw', out, k3, C3, hs', hf, hm, r3⟩ := hr
      simp only [WithdrawReservesRun]
      by_cases hp : evm'.executionEnv.perm = true
      · rw [if_pos hp]
        rw [← hs'.accounts]
        exact cometWithExtendedAssetList_block_6302 (immWords := wordsOf (immStore v))
          (by omega) (by rwa [hs'.env] at hp) r3
      · rw [if_neg hp]
        exact cometWithdrawReservesLogStatic (by omega)
          (by rw [hs'.env] at hp; exact Bool.eq_false_iff.mpr hp) r3
  · exact ⟨none, .checksFailed hv, r1⟩

theorem cometWithdrawReservesQuery {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {free amount mask : UInt256} {R : List UInt256}
    {recipient : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 38 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = free)
    (hlo : 96 ≤ free.toNat) (hb : free.toNat + 100 < 2^64)
    (ha : evm.executionEnv.source = v.governor) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6201⟩
      (mask :: EVM.word recipient.val :: amount :: R) mem aw rdata σ k C) :
    ∃ result, WithdrawReservesTrace v recipient amount evm result ∧
      WithdrawReservesRun v g s0 result := by
  have r1 := cometWithExtendedAssetList_block_6201
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨result, ht, hr⟩ := cometReservesTrace (v := v)
    (by change R.length + 3 + 35 ≤ 1024; omega) hfree hlo (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨none, .reservesFailed ha ht, hr⟩
  | some result =>
    rcases result with ⟨evm', reserves⟩
    obtain ⟨σ', mem', aw', out, k2, C2, hs', hf, r2⟩ := hr
    have hptr : (free + (⟨32⟩ : UInt256)).toNat = free.toNat + 32 :=
      uadd_word_ofNat_toNat free 32 (by change free.toNat + 32 < 2^256; omega)
    obtain ⟨result, ht', hr'⟩ := cometWithdrawReservesAfter (by omega) hf
      (by rw [hptr]; omega) (by rw [hptr]; omega) hs' r2
    exact ⟨result, .reservesOk ha ht ht', hr'⟩

end Benchmarks.CompoundIII.Comet
