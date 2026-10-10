import Benchmarks.CompoundIII.Comet.TransferInModel
import Benchmarks.CompoundIII.Comet.TransferFromMemory
import Benchmarks.CompoundIII.Comet.TransferInResponse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferInCall {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr amount dummy : UInt256} {R : List UInt256}
    {asset sender : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 10 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hb : ptr.toNat + 100 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13340⟩
      (dummy :: EVM.word sender.val :: amount :: EVM.word asset.val :: ⟨32⟩ :: R)
      mem aw rdata σ k C) :
    ∃ result, TransferCallTrace asset
        (transferFromPayload sender evm.executionEnv.codeOwner amount) evm result ∧
      match result with
      | none => RDrev (deployedRuntime v) g s0
      | some (evm', out) => TransferReturnValid out ∧ ∃ σ' aw' k' C',
          SourceState s0 ee σ' evm' ∧
          RD (deployedRuntime v) ee g s0 ⟨13449⟩ (EVM.word asset.val :: ⟨32⟩ :: R)
            (transferFromOutputMemory mem ptr sender ee.codeOwner amount out) aw' out σ' k' C' := by
  by_cases hc : extCodeSizeWord σ (EVM.word asset.val) = ⟨0⟩
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_13340_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by rw [hc]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨none, .codeMissing (by simpa only [hs.accounts] using hc),
      cometRevert1410 (by change R.length + 4 + 2 ≤ 1024; omega) r1⟩
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_13340_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (isZero_eq_zero_of_ne hc) h
    have r2 := cometWithExtendedAssetList_block_13349 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 9 ≤ 1024; omega) r1
    have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
    have hsender : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
        (EVM.word sender.val) = EVM.word sender.val :=
      solcAddrMask_clean_left (addressWord_val_canonical sender)
    simp only [cometWithExtendedAssetList_block_13349_stack,
      cometWithExtendedAssetList_block_13349_memory, hf, hsender] at r2
    change RD _ _ _ _ _ _ (transferFromInputMemory mem ptr sender ee.codeOwner amount)
      _ _ _ _ _ at r2
    obtain ⟨evm', σ', z, out, k3, C3, hcall, hs', r3, hh⟩ := zeroCallBridge r2 hs
      (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
        wordsOf (immStore v), (⟨13402⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
        immutableLayout_inBounds, immutableTemplate_size64))
      (transferFromInputMemory_payload hb) (by rw [transferFromPayload_size]; decide)
      (by change R.length + 3 + 1 ≤ 1024; omega)
    have hcall' : callViaEVM evm asset 0
        (transferFromPayload sender evm.executionEnv.codeOwner amount) (z, evm', out) := by
      have haddr : AccountAddress.ofUInt256 (EVM.word asset.val) = asset :=
        accountAddress_roundtrip asset
      simpa only [haddr, hs.env] using hcall
    have ht := TransferCallTrace.callResult (by simpa only [hs.accounts] using hc)
      hcall' (lt_trans hh (by decide))
    change RD _ _ _ _ ⟨13403⟩ _
      (callOutputMem (transferFromInputMemory mem ptr sender ee.codeOwner amount) out ptr ⟨0⟩)
      _ _ _ _ _ at r3
    rw [callOutputMem_zero] at r3
    rcases cometTransferInResponse (v := v) hstack
      (lt_trans hh (by change 2^138 < 2^256; decide)) (by omega) r3 with
      ⟨hz, hv, aw4, k4, C4, r4⟩ | ⟨hv, r4⟩
    · rw [if_pos ⟨hz, hv⟩] at ht
      exact ⟨some (evm', out), ht, hv, σ', aw4, k4, C4, hs', r4⟩
    · rw [if_neg hv] at ht
      exact ⟨none, ht, r4⟩

end Benchmarks.CompoundIII.Comet
