import Benchmarks.CompoundIII.Comet.TransferInCallEvm
import Benchmarks.CompoundIII.Comet.TransferInBalanceBefore
import Benchmarks.CompoundIII.Comet.TransferInBalanceAfter
import Benchmarks.CompoundIII.Comet.CheckedSub256Evm
import Benchmarks.CompoundIII.Comet.AssetCallMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def TransferInRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret free : UInt256) (R : List UInt256)
    (result : Option (EVM.State × UInt256)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', value) => ∃ σ' mem aw out k C, SourceState s0 ee σ' evm' ∧
      memLoad ⟨64⟩ mem = free ∧ free.toNat ≤ mem.size ∧
      RD (deployedRuntime v) ee g s0 ret (value :: R) mem aw out σ' k C

theorem cometTransferInAfter {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr amount pre dummy ret : UInt256} {R : List UInt256}
    {asset sender : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 16 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 100 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13340⟩
      (dummy :: EVM.word sender.val :: amount :: EVM.word asset.val :: ⟨32⟩ :: pre ::
        tokenBalanceSelectorWord :: ret :: R) mem aw rdata σ k C) :
    ∃ result, TransferInAfter asset sender amount pre evm result ∧
      TransferInRun v ee g s0 ret (ptr + ⟨32⟩) R result := by
  obtain ⟨result, ht, hr⟩ := cometTransferInCall (v := v)
    (by change R.length + 3 + 10 ≤ 1024; omega) hfree hb hs h
  cases result with
  | none => exact ⟨none, .transferFailed ht, hr⟩
  | some r =>
    obtain ⟨evm', transferOut⟩ := r
    obtain ⟨hv, σ', aw1, k1, C1, r1hs, r1⟩ := hr
    obtain ⟨evm'', σ'', z, out, hc, hs'', hh, hr⟩ := cometTransferInBalanceAfter (v := v)
      (by change R.length + 1 + 15 ≤ 1024; omega) (transferFromOutputMemory_free hv)
      hlo (by omega) r1hs r1
    have hbalance := TokenBalanceTrace.response hc (lt_trans hh (by decide))
    by_cases hvalid : z = true ∧ 32 ≤ out.size
    · rw [if_pos hvalid] at hr hbalance
      have htrace := TransferInAfter.balanceResult (pre := pre) ht hbalance
      obtain ⟨aw2, k2, C2, r2⟩ := hr
      have hsub := cometCheckedSub256 (v := v) (by change R.length + 1 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
      by_cases hle : pre.toNat ≤ (calldataWord out 0).toNat
      · rw [if_pos hle] at htrace hsub
        obtain ⟨k3, C3, r3⟩ := hsub
        have r4 := cometWithExtendedAssetList_block_2425 (immWords := wordsOf (immStore v))
          (by omega) hret r3
        refine ⟨_, htrace, σ'', _, aw2, out, _, _, hs'', ?_, ?_, r4⟩
        · exact memLoad_writeWord_self _ ⟨64⟩ _
        · have hhi : out.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
          rw [tokenBalanceReturnMemory_size hlo (by change ptr.toNat + 36 < 2^256; omega) hhi]
          have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
            uadd_word_ofNat_toNat ptr 32 (by change ptr.toNat + 32 < 2^256; omega)
          rw [hp]
          omega
      · rw [if_neg hle] at htrace hsub
        exact ⟨none, htrace, hsub⟩
    · rw [if_neg hvalid] at hr hbalance
      exact ⟨none, .balanceFailed ht hbalance, hr⟩

theorem cometTransferInInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr amount ret : UInt256} {R : List UInt256}
    {asset sender : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 16 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 132 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13272⟩
      (EVM.word asset.val :: EVM.word sender.val :: amount :: ret :: R) mem aw rdata σ k C) :
    ∃ result, TransferInTrace asset sender amount evm result ∧
      TransferInRun v ee g s0 ret (ptr + ⟨64⟩) R result := by
  obtain ⟨evm', σ', z, out, hc, hs', hh, hr⟩ := cometTransferInBalanceBefore (v := v)
    (by change R.length + 1 + 15 ≤ 1024; omega) hfree hlo (by omega) hs h
  have hbalance := TokenBalanceTrace.response hc (lt_trans hh (by decide))
  by_cases hvalid : z = true ∧ 32 ≤ out.size
  · rw [if_pos hvalid] at hr hbalance
    obtain ⟨aw1, k1, C1, dummy, r1⟩ := hr
    have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
      uadd_word_ofNat_toNat ptr 32 (by change ptr.toNat + 32 < 2^256; omega)
    obtain ⟨result, ht, hr⟩ := cometTransferInAfter (v := v) hstack
      (memLoad_writeWord_self _ ⟨64⟩ _) (by rw [hp]; omega) (by rw [hp]; omega) hret hs' r1
    have hp2 : (ptr + ⟨32⟩) + ⟨32⟩ = ptr + ⟨64⟩ := by rw [u256_add_assoc]; rfl
    rw [hp2] at hr
    exact ⟨result, .balanceOk hbalance ht, hr⟩
  · rw [if_neg hvalid] at hr hbalance
    exact ⟨none, .balanceFailed hbalance, hr⟩

end Benchmarks.CompoundIII.Comet
